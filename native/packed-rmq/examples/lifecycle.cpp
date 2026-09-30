#include "packed_rmq_lifecycle.h"

#include <cstdio>
#include <cstring>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
#if defined(_WIN32)
#include <fcntl.h>
#include <io.h>
#endif

namespace {

// All calls and destructors stay on main's initializing thread. These owners
// cannot be copied; foreign callers must obey the C ABI's uniqueness contract.
struct Owner {
    packed_lifecycle_owner *value = nullptr;
    Owner() = default;
    Owner(const Owner &) = delete;
    Owner &operator=(const Owner &) = delete;
    ~Owner() { packed_lifecycle_owner_free(&value); }
};

struct Result {
    packed_lifecycle_result *value = nullptr;
    Result() = default;
    Result(const Result &) = delete;
    Result &operator=(const Result &) = delete;
    ~Result() { packed_lifecycle_result_free(value); }
};

struct Observation {
    packed_lifecycle_observation *value = nullptr;
    Observation() = default;
    Observation(const Observation &) = delete;
    Observation &operator=(const Observation &) = delete;
    ~Observation() { packed_lifecycle_observation_free(value); }
};

void require(bool condition, const std::string &label) {
    if (!condition) throw std::runtime_error(label);
}

void checked(int status, const char *operation) {
    if (status != PACKED_LIFECYCLE_OK) {
        throw std::runtime_error(std::string(operation) + " status=" + std::to_string(status));
    }
}

packed_lifecycle_bytes view(const std::vector<uint8_t> &bytes) {
    return {bytes.data(), bytes.size()};
}

// The fixture's endpoints are single-byte literals. Their representation is
// zero-padded to the actual query-independent profile returned by the DLL.
std::vector<uint8_t> endpoint(size_t bytes, uint8_t literal) {
    require(bytes != 0, "profile empty endpoint width");
    std::vector<uint8_t> result(bytes, 0);
    result[0] = literal;
    return result;
}

void check_packet(const Result &result, size_t width_bytes, uint8_t expected,
                  const char *label) {
    require(result.value != nullptr, std::string(label) + " missing result");
    const auto bytes = packed_lifecycle_result_bytes(result.value);
    require(bytes.data != nullptr && bytes.size == width_bytes,
            std::string(label) + " packet representation");
    require(bytes.data[0] == expected, std::string(label) + " packet low byte");
    for (size_t i = 1; i < bytes.size; ++i) {
        require(bytes.data[i] == 0, std::string(label) + " packet high byte");
    }
}

size_t inspect(const Owner &owner, size_t width_bits, size_t expected_extent,
               const char *label) {
    require(owner.value != nullptr, std::string(label) + " missing owner");
    packed_lifecycle_info info{};
    checked(packed_lifecycle_inspect(owner.value, &info), "inspect");
    require(info.count == 4 && info.width_bits == width_bits,
            std::string(label) + " produced metadata");
    require(info.memory_extent != 0 && info.arrays[1].initialized == info.memory_extent,
            std::string(label) + " memory extent");
    if (expected_extent != 0) {
        require(info.memory_extent == expected_extent, std::string(label) + " preserved extent");
    }
    require(info.arrays[0].initialized == 8273, std::string(label) + " numeric bank");
    require(info.arrays[2].initialized == 0 && info.arrays[3].initialized == 0,
            std::string(label) + " retired key banks");
    require(info.exclusive_owner == 1 && info.exact_capacities == 1 &&
                info.no_retained_operational_roots == 1,
            std::string(label) + " publication predicate");

    // A zero-capacity array exposes the requested header storage. Check the
    // header+capacity*pointer accounting uniformly, including both empty banks.
    // These requested bytes do not claim allocator usable bytes or RSS.
    const size_t header_bytes = info.arrays[2].requested_bytes;
    require(header_bytes != 0 && info.arrays[3].requested_bytes == header_bytes,
            std::string(label) + " empty container storage");
    for (size_t i = 0; i != 4; ++i) {
        const auto &array = info.arrays[i];
        require(array.initialized == array.capacity && array.identity != 0,
                std::string(label) + " exact array capacity " + std::to_string(i));
        require(array.capacity <= (std::numeric_limits<size_t>::max() - header_bytes) / sizeof(void *),
                std::string(label) + " requested byte overflow");
        require(array.requested_bytes == header_bytes + array.capacity * sizeof(void *),
                std::string(label) + " requested array bytes " + std::to_string(i));
    }
    return info.memory_extent;
}

void later(Owner &owner, size_t width_bits, size_t width_bytes, size_t extent,
           uint8_t left, uint8_t right, uint8_t expected, const char *label) {
    const auto encoded_left = endpoint(width_bytes, left);
    const auto encoded_right = endpoint(width_bytes, right);
    Result answer;
    Observation diagnostics;
    checked(packed_lifecycle_query(&owner.value, view(encoded_left), view(encoded_right), 0,
                                  &answer.value, &diagnostics.value), label);
    require(diagnostics.value == nullptr, std::string(label) + " unexpected diagnostics");
    check_packet(answer, width_bytes, expected, label);
    inspect(owner, width_bits, extent, label);
}

void exercise(uint8_t model) {
    checked(packed_lifecycle_init(), "initialize");
    size_t width_bits = 0, width_bytes = 0;
    checked(packed_lifecycle_profile(4, &width_bits, &width_bytes), "profile");
    require(width_bits >= 3 && width_bytes == (width_bits + 7) / 8, "profile width relation");

    const uint8_t three = 3, one = 1, seven = 7;
    const packed_lifecycle_int input[] = {
        {0, {&three, 1}}, {1, {&one, 1}}, {1, {&one, 1}}, {0, {&seven, 1}}
    };
    const auto left = endpoint(width_bytes, 0);
    const auto right = endpoint(width_bytes, 4);
    Owner owner;
    size_t extent = 0;
    {
        Result answer;
        Observation diagnostics;
        checked(packed_lifecycle_build_first(model, input, 4, view(left), view(right), 0,
                                            &owner.value, &answer.value, &diagnostics.value),
                "build-first");
        require(diagnostics.value == nullptr, "build-first unexpected diagnostics");
        // Independent expectations for [3,-1,-1,7]: first minimum index1;
        // reversed range has no answer; [2,4) has minimum index2.
        check_packet(answer, width_bytes, 2, "build-first");
        extent = inspect(owner, width_bits, 0, "build-first");
    }
    later(owner, width_bits, width_bytes, extent, 3, 1, 0, "invalid-query");
    later(owner, width_bits, width_bytes, extent, 2, 4, 3, "valid-after-invalid");
    // Owner, result and diagnostic wrappers all destroy on this same thread,
    // including any exception path and an ABI post-take empty-owner failure.
}

} // namespace

int main(int argc, char **argv) {
#if defined(_WIN32)
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
#endif
    try {
        require(argc == 2, "usage: lifecycle_cpp word|comparison");
        const bool word = std::strcmp(argv[1], "word") == 0;
        require(word || std::strcmp(argv[1], "comparison") == 0,
                "usage: lifecycle_cpp word|comparison");
        exercise(word ? PACKED_LIFECYCLE_WORD : PACKED_LIFECYCLE_COMPARISON);
        std::printf("LIFE-NATIVE1 CPP %s PASS\n", word ? "word" : "comparison");
        return 0;
    } catch (const std::exception &error) {
        std::fprintf(stderr, "LIFE-NATIVE1 CPP FAIL %s\n", error.what());
        return 1;
    }
}
