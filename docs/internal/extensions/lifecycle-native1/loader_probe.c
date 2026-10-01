/* Loader-only diagnostic: no lifecycle initializer or query is invoked. */
#include <windows.h>
#include <stdio.h>
#include <fcntl.h>
#include <io.h>
int main(int argc, char **argv) {
    _setmode(_fileno(stdout), _O_BINARY);
    _setmode(_fileno(stderr), _O_BINARY);
    if (argc != 2) return 2;
    SetErrorMode(SEM_FAILCRITICALERRORS | SEM_NOGPFAULTERRORBOX | SEM_NOOPENFILEERRORBOX);
    fputs("LIFE-NATIVE1 LOADER START\n", stdout); fflush(stdout);
    HMODULE module = LoadLibraryA(argv[1]);
    DWORD error = module ? ERROR_SUCCESS : GetLastError();
    printf("LIFE-NATIVE1 LOADER loaded=%d error=%lu\n", module != NULL, (unsigned long)error);
    if (module) {
        printf("LIFE-NATIVE1 LOADER initSymbol=%d\n", GetProcAddress(module, "packed_lifecycle_init") != NULL);
        FreeLibrary(module);
    }
    return 0;
}
