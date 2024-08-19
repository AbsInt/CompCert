# Tell the tools to use only ASCII in diagnostic outputs
export LC_ALL=C

# Stop on error
set -e

# Simulators

simu_aarch64="qemu-aarch64 -L /usr/aarch64-linux-gnu"
simu_armsf="qemu-arm -L /usr/arm-linux-gnueabi"
simu_armhf="qemu-arm -L /usr/arm-linux-gnueabihf"
simu_ppc32="qemu-ppc -L /usr/powerpc-linux-gnu -cpu G4"
simu_rv64="qemu-riscv64 -L /usr/riscv64-linux-gnu"
# simu_x86_32="qemu-i386 -L /usr/i686-linux-gnu"

# Fatal error

Fatal() {
  echo "FATAL ERROR: $@" 1>&2
  exit 2
}

# Validate input parameters

if test -z "$target"; then Fatal 'Missing $target value'; fi
if test -z "$os"; then Fatal 'Missing $os value'; fi
if test -z "$jobs"; then jobs=1; fi

# Set up OPAM (if requested)

if test -n "$opamroot"; then
  export OPAMROOT="$opamroot"
  eval `opam env --safe`
fi

# Install additional system packages

System_install() {
  case "$target,$os" in
    aarch64,linux)
      sudo apt-get update
      sudo apt-get -y install qemu-user gcc-aarch64-linux-gnu
      ;;
    arm,linux)
      sudo apt-get update
      sudo apt-get -y install qemu-user gcc-arm-linux-gnueabi gcc-arm-linux-gnueabihf
      ;;
    ppc,linux)
      sudo apt-get update
      sudo apt-get -y install qemu-user gcc-powerpc-linux-gnu
      ;;
    riscv,linux)
      sudo apt-get update
      sudo apt-get -y install qemu-user gcc-riscv64-linux-gnu
      ;;
    x86_32,linux)
      sudo apt-get update
      sudo apt-get -y install gcc-multilib
      ;;
    x86_64,linux)
      ;;
    aarch64,macos)
      ;;
    x86_64,macos)
      ;;
    x86_32,windows)
      ;;
    x86_64,windows)
      ;;
  esac
}

# Install additional OPAM packages

OPAM_install() {
  if test -n "$*"; then
    opam install -y $*
  fi
}

# Run configure script

Configure() {
  echo "Configuration parameters:"
  echo "    Target architecture \"$target\" (variable \$target)"
  echo "    Host OS \"$os\" (variable \$os)"
  echo "    Configure options \"$configopts\" (variable \$configopts)"
  echo ""
  case "$target,$os" in
    aarch64,linux)
      ./configure $configopts -toolprefix aarch64-linux-gnu- aarch64-linux
      ;;
    arm,linux)
      ./configure $configopts -toolprefix arm-linux-gnueabihf- arm-eabihf
      ;;
    ppc,linux)
      ./configure $configopts -toolprefix powerpc-linux-gnu- ppc-linux
      ;;
    riscv,linux)
      ./configure $configopts -toolprefix riscv64-linux-gnu- rv64-linux
      ;;
    x86_32,linux)
      ./configure $configopts x86_32-linux
      ;;
    x86_64,linux)
      ./configure $configopts -clightgen x86_64-linux
      ;;
    aarch64,macos)
      ./configure $configopts -clightgen aarch64-macos
      ;;
    x86_64,macos)
      ./configure $configopts x86_64-macos
      ;;
    x86_32,windows)
      ./configure $configopts x86_32-cygwin
      ;;
    x86_64,windows)
      ./configure $configopts x86_64-cygwin
      ;;
    *)
      Fatal "Unknown configuration \"$target\" - \"$os\""
      ;;
  esac
}

# Full build (including standard library)

Build_all() {
  make -j$jobs all
}

# Coq + OCaml build (no standard library)

Build_ccomp() {
  make depend
  make -j$jobs proof
  make -j$jobs ccomp
}

# Recheck proof using coqchk

Check_proof() {
  output=`mktemp`
  trap "rm -f $output" 0 INT
  if make check-proof > $output 2>&1
  then echo "Check proof: success"
  else echo "Check proof: FAILURE"; cat $output; exit 2
  fi
}

# Rebuild compcert.ini and the standard library with a different configuration
# Don't rebuild ccomp

Rebuild_runtime() {
  ./configure $*
  make compcert.ini
  make -C runtime -s clean
  make -C runtime -j$jobs all
}

# Run the test suite.
# First parameter: name of simulator to use (if any)
# Second parameter: compilation options (if any)

Run_test() {
  make -C test -s clean
  make -C test CCOMPOPTS="$2" -j$jobs all
  make -C test SIMU="$1" test
}

# Rounds of testing.
# First parameter: round number (1, 2, ...)

Run_test_round() {
case "$target,$os" in
  aarch64,linux)
    case "$1" in
      1) Run_test "$simu_aarch64" "";;
      2) Run_test "$simu_aarch64" "-Os";;
    esac;;
  aarch64,macos)
    case "$1" in
      1) Run_test "" "";;
      2) Run_test "" "-Os";;
    esac;;
  arm,linux)
    # TEMPORARY: skip ARM testing because of QEMU problem on the test VM
    # case "$1" in
    #   1) Run_test "$simu_armhf" "-marm";;
    #   2) Run_test "$simu_armhf" "-mthumb";;
    #   3) Rebuild_runtime -toolprefix arm-linux-gnueabi- arm-eabi
    #      Run_test "$simu_armsf" "-marm";;
    # esac;;
    echo "Skipping ARM tests";;
  ppc,linux)
    # TEMPORARY: skip PPC testing because of QEMU problem on the test VM
    # case "$1" in
    #   1) Run_test "$simu_ppc32" "";;
    #   2) Run_test "$simu_ppc32" "-Os";;
    # esac;;
    echo "Skipping PPC tests";;
  riscv,linux)
    case "$1" in
      1) Run_test "$simu_rv64" "";;
      2) Run_test "$simu_rv64" "-Os";;
    esac;;
  x86_32,*|x86_64,*)
    case "$1" in
      1) Run_test "" "";;
      2) Run_test "" "-Os";;
    esac;;
  *)
    Fatal "Unknown configuration \"$target\" - \"$os\""
esac
}

# Check for things that should not be in the Coq sources (admits, etc)

Hygiene () {
  make check-admitted && make check-leftovers
}

case "$1" in
  system_install) System_install;;
  opam_install) shift; OPAM_install "$@";;
  configure) Configure;;
  build) Build_all;;
  test1) Run_test_round 1;;
  test2) Run_test_round 2;;
  test3) Run_test_round 3;;
  build_ccomp) Build_ccomp;;
  check_proof) Check_proof;;
  hygiene) Hygiene;;
  *) Fatal "Unknown CI instruction: $1"; exit 1;;
esac

