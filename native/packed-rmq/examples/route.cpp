#include "../include/packed_rmq_route.h"
#include <fstream>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>

static std::string read_file(const char *path) {
    std::ifstream f(path, std::ios::binary);
    if (!f) throw std::runtime_error("cannot read input");
    std::ostringstream s;
    s << f.rdbuf();
    return s.str();
}
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    try {
        const auto program = read_file(argv[1]);
        const auto fixture = read_file(argv[2]);
        if (packed_route_init()) return 3;
        void *result = packed_route_eval(program.c_str(), program.size(), fixture.c_str(), fixture.size(), 1);
        if (!result) return 4;
        std::cout << packed_route_text(result);
        packed_route_free(result);
        return 0;
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 5;
    }
}
