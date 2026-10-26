# CompCert security policy

## Reporting security issues

If you discover a security vulnerability, we'd appreciate a non-public disclosure. The CompCert developers can be contacted privately by creating a new [Security Advisory on GitHub](https://github.com/AbsInt/CompCert/security/advisories/new).

## What is a security issue

The following issues are security issues and should be disclosed responsibly as described above:
- Any case of miscompilation, where CompCert silently generates executable code that does not behave as prescribed by the source C code.  (Despite CompCert's extensive formal verification, bugs in the unverified parts of CompCert or in the formal modeling of target processors can still result in miscompilation.)

The following issues are not security issues, just quality of implementation issues, and can be reported on the [public issue tracker](https://github.com/AbsInt/CompCert/issues):
- Compile-time errors (failed assertions, uncaught exceptions, etc) where CompCert stops before generating executable code.
- Compiler runs that take a very long time or use a lot of memory.

The following situations are not CompCert issues, just normal behavior for a C compiler, and should not be reported at all:
- Source code containing undefined behaviors is compiled to an executable that does not crash at run-time.
- Compiled code crashes at run-time because the stack overflows.

## Supported versions

For the public version of CompCert, only the latest release is supported.  Older releases do not receive security fixes.

For the commercial version of CompCert distributed by AbsInt, long-term support is available; check with AbsInt.

