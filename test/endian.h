#if defined(__ppc__) || defined(__PPC__) || defined(__ARMEB__)
#define ARCH_BIG_ENDIAN
#elif defined(__i386__) || defined(__x86_64__) || defined(__ARMEL__) \
   || defined(__riscv) || defined(__aarch64__)
#undef ARCH_BIG_ENDIAN
#else
#error "unknown endianness"
#endif
