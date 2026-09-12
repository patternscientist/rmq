#include "../include/packed_rmq.h"

#include <array>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <limits>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

namespace {
constexpr std::size_t max_image_bytes = 134217728;
constexpr std::size_t max_endpoint_bytes = 512;
constexpr std::size_t max_fuel = 1000000;
constexpr const char *usage =
    "usage: packed-rmq-native load IMAGE | query IMAGE LEFT_HEX RIGHT_HEX FUEL READS [REPEAT]";

using Bytes = std::vector<std::uint8_t>;
using LoadOwner = std::unique_ptr<packed_rmq_load_result, decltype(&packed_rmq_load_free)>;
using QueryOwner = std::unique_ptr<packed_rmq_query_result, decltype(&packed_rmq_query_free)>;

const std::uint8_t *span_data(const Bytes &bytes) {
    static const std::uint8_t empty = 0;
    return bytes.empty() ? &empty : bytes.data();
}

std::size_t natural(const std::string &text, const char *name) {
    const auto invalid = std::string("invalid ") + name;
    if (text.empty()) throw std::runtime_error(invalid);
    std::size_t value = 0;
    for (const unsigned char byte : text) {
        if (byte < '0' || byte > '9') throw std::runtime_error(invalid);
        const auto digit = static_cast<std::size_t>(byte - '0');
        if (value > (std::numeric_limits<std::size_t>::max() - digit) / 10)
            throw std::runtime_error(invalid);
        value = value * 10 + digit;
    }
    return value;
}

unsigned nibble(unsigned char byte) {
    if (byte >= '0' && byte <= '9') return byte - '0';
    if (byte >= 'a' && byte <= 'f') return byte - 'a' + 10;
    if (byte >= 'A' && byte <= 'F') return byte - 'A' + 10;
    throw std::runtime_error("invalid endpoint hex");
}

Bytes hex_bytes(const std::string &text) {
    if (text.size() > 2 * max_endpoint_bytes || text.size() % 2 != 0)
        throw std::runtime_error("invalid endpoint hex");
    Bytes result;
    result.reserve(text.size() / 2);
    for (std::size_t offset = 0; offset < text.size(); offset += 2)
        result.push_back(static_cast<std::uint8_t>(
            nibble(static_cast<unsigned char>(text[offset])) * 16 +
            nibble(static_cast<unsigned char>(text[offset + 1]))));
    return result;
}

Bytes read_image(const char *path) {
    std::error_code error;
    const auto size = std::filesystem::file_size(path, error);
    if (error) throw std::runtime_error(error.message());
    if (size > max_image_bytes) throw std::runtime_error("image byte limit");
    std::ifstream file(path, std::ios::binary);
    if (!file) throw std::runtime_error("cannot read input");
    Bytes bytes;
    bytes.reserve(static_cast<std::size_t>(size));
    std::array<char, 65536> buffer{};
    while (file) {
        file.read(buffer.data(), static_cast<std::streamsize>(buffer.size()));
        const auto count = static_cast<std::size_t>(file.gcount());
        if (count > max_image_bytes - bytes.size())
            throw std::runtime_error("image byte limit");
        bytes.insert(bytes.end(), buffer.begin(), buffer.begin() + count);
    }
    if (!file.eof()) throw std::runtime_error("cannot read input");
    return bytes;
}

bool valid_utf8(const std::string &text) {
    std::size_t offset = 0;
    while (offset < text.size()) {
        const auto lead = static_cast<unsigned char>(text[offset++]);
        if (lead < 0x80) continue;
        unsigned remaining;
        std::uint32_t value;
        std::uint32_t minimum;
        if (lead >= 0xc2 && lead <= 0xdf) {
            remaining = 1; value = lead & 0x1f; minimum = 0x80;
        } else if (lead >= 0xe0 && lead <= 0xef) {
            remaining = 2; value = lead & 0x0f; minimum = 0x800;
        } else if (lead >= 0xf0 && lead <= 0xf4) {
            remaining = 3; value = lead & 0x07; minimum = 0x10000;
        } else {
            return false;
        }
        if (remaining > text.size() - offset) return false;
        while (remaining-- != 0) {
            const auto byte = static_cast<unsigned char>(text[offset++]);
            if ((byte & 0xc0) != 0x80) return false;
            value = (value << 6) | (byte & 0x3f);
        }
        if (value < minimum || value > 0x10ffff || (value >= 0xd800 && value <= 0xdfff))
            return false;
    }
    return true;
}

std::string copy_text(const char *pointer) {
    if (!pointer) throw std::runtime_error("native text handle missing");
    std::string text(pointer);
    if (!valid_utf8(text)) throw std::runtime_error("non-UTF8 native result");
    return text;
}

void execute(int argc, char **argv) {
    const bool is_load = argc == 3 && std::string(argv[1]) == "load";
    const bool is_query = (argc == 7 || argc == 8) && std::string(argv[1]) == "query";
    if (!is_load && !is_query) throw std::runtime_error(usage);

    Bytes left, right;
    std::size_t fuel = 0, repeat = 1;
    std::uint8_t reads = 0;
    if (is_query) {
        left = hex_bytes(argv[3]);
        right = hex_bytes(argv[4]);
        fuel = natural(argv[5], "fuel");
        const std::string read_argument(argv[6]);
        if (read_argument == "1") reads = 1;
        else if (read_argument != "0") throw std::runtime_error("reads must be 0 or 1");
        if (argc == 8) repeat = natural(argv[7], "repeat");
        if (repeat < 1 || repeat > 16)
            throw std::runtime_error("repeat must be between 1 and 16");
    }

    auto bytes = read_image(argv[2]);
    if (packed_rmq_init() != 0) throw std::runtime_error("Lean initialization failed");
    // All calls, borrowed views and owning-handle destruction stay on this thread.
    LoadOwner owner(packed_rmq_load(span_data(bytes), bytes.size()), &packed_rmq_load_free);
    if (!owner) throw std::runtime_error("native load bridge failure");
    if (packed_rmq_load_status(owner.get()) != 0)
        throw std::runtime_error(copy_text(packed_rmq_load_error(owner.get())));
    const auto *image = packed_rmq_loaded_image(owner.get());
    if (!image) throw std::runtime_error("native image handle missing");
    Bytes().swap(bytes);

    if (is_load) {
        std::cout << "loaded " << packed_rmq_word_bytes(image) << '\n';
        return;
    }
    for (std::size_t attempt = 0; attempt < repeat; ++attempt) {
        if (left.size() > max_endpoint_bytes || right.size() > max_endpoint_bytes || fuel > max_fuel)
            throw std::runtime_error("query host limit");
        QueryOwner result(packed_rmq_query(image, span_data(left), left.size(),
            span_data(right), right.size(), fuel, reads), &packed_rmq_query_free);
        if (!result) throw std::runtime_error("native query bridge failure");
        const auto text = copy_text(packed_rmq_query_text(result.get()));
        const auto status = packed_rmq_query_status(result.get());
        if (status == 1) throw std::runtime_error(text);
        if (status != 0) throw std::runtime_error("invalid native query status");
        std::cout << text;
    }
}
} // namespace

int main(int argc, char **argv) {
    try {
#ifdef _WIN32
        if (_setmode(_fileno(stdout), _O_BINARY) == -1 ||
            _setmode(_fileno(stderr), _O_BINARY) == -1)
            throw std::runtime_error("cannot configure binary output");
#endif
        execute(argc, argv);
        return 0;
    } catch (const std::exception &error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
