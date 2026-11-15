#!/usr/bin/env bash
# Copyright 2026 Andrew Yates
# SPDX-License-Identifier: Apache-2.0 OR MIT
# Author: Andrew Yates <andrewyates.name@gmail.com>
#
# Cargo rustc-wrapper for Trust-MC's out-of-tree rustc_private crates.
#
# Trust's installed sysroot can omit the coherent rustc-dev dependency closure
# used to build the compiler.  Bootstrap preserves that closure under a
# rustc-private-sysroots directory.  This wrapper overlays the exact private
# sysroot whose rustc_driver hash matches the active Trust compiler, without
# mutating the shared toolchain.
#
# The overlay is OPT-IN: it arms only when TRUST_PRIVATE_SYSROOTS names at
# least one snapshot directory.  Otherwise every invocation passes straight
# through to the compiler Cargo selected.  A sealed Trust toolchain whose own
# target libdir already carries a coherent rustc-dev closure (measured on the
# 25ccaf01f seal, 2026-09-10: the six rustc_private crates reach type checking
# with no overlay) needs no snapshot, and demanding one there failed every
# rustc_private crate closed before compilation.  An explicit configuration is
# honoured strictly: only the configured roots are searched, and when none of
# them holds a snapshot matching the active driver hash that is a hard error,
# never a silent fallback to a snapshot discovered somewhere else.
set -eu

if [ "$#" -lt 1 ]; then
    echo "trustc-private-wrapper: missing rustc argument" >&2
    exit 2
fi

RUSTC="$1"
shift

if [ -z "${TRUST_PRIVATE_SYSROOTS:-}" ]; then
    exec "$RUSTC" "$@"
fi

REPO="$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)"
CACHE_ROOT="${CARGO_TARGET_DIR:-$REPO/target}"
# This fixed list belongs to the wrapper, not Cargo's environment table or
# caller input. Scanner has library/binary spellings; build_trust_mc has no
# rustc_private dependency and must retain the ordinary compiler sysroot.
DRIVER_CRATES="trust_mc_compiler trust_mc_codegen_shared trust_mc_codegen_types trust_mc_kani_types scanner scan trust_mc_engine rustc_codegen_trust_mc"

is_driver_crate() {
    crate_name=""
    previous=""
    for argument in "$@"; do
        case "$previous" in
            --crate-name) crate_name="$argument" ;;
        esac
        case "$argument" in
            --crate-name=*) crate_name="${argument#--crate-name=}" ;;
        esac
        previous="$argument"
    done
    case " $DRIVER_CRATES " in
        *" $crate_name "*) [ -n "$crate_name" ] ;;
        *) return 1 ;;
    esac
}

# Cargo applies rustc-wrapper workspace-wide, but only these explicitly named
# targets consume rustc_private. Keep ordinary dependencies and all public
# rustc_private-free packages on the unmodified pinned sysroot. This also lets
# Cargo's `rustc -vV`/`--print` probes run on hosts that intentionally lack the
# private bootstrap snapshot.
if ! is_driver_crate "$@"; then
    exec "$RUSTC" "$@"
fi

# The overlay exists because the TRUST compiler keeps its rustc_private
# dependency closure in a separate rustc-private-tool sysroot, so building
# against its ordinary sysroot fails on skewed shared crates (the E0460
# hashbrown error).  A stock rustup toolchain carrying the `rustc-dev`
# component has no such split -- its private closure IS its target libdir --
# and these same six crates build against it directly.  That is not
# hypothetical: trust-mc's Kani-compatibility lane builds trust-mc-compiler on
# the frozen `nightly-2025-12-03` (docs/KANI-LANE-REVIVAL.md), and on
# 2026-09-01 that lane produced a working 59 MB verifier.  Demanding a Trust
# private snapshot from a compiler that neither has nor needs one fails closed
# on the ONLY toolchain currently able to build this crate, so the overlay is
# scoped to the Trust compiler, identified the way it identifies itself.
if ! "$RUSTC" --version --verbose 2>/dev/null | grep -q '^trust:'; then
    exec "$RUSTC" "$@"
fi

active_sysroot="$("$RUSTC" --print sysroot)"

# Whether the arguments build a cdylib (`--crate-type cdylib`, either spelling).
is_cdylib() {
    previous=""
    for argument in "$@"; do
        case "$previous" in
            --crate-type) [ "$argument" = "cdylib" ] && return 0 ;;
        esac
        case "$argument" in
            --crate-type=cdylib) return 0 ;;
        esac
        previous="$argument"
    done
    return 1
}

emit_and_exec() {
    overlay="$1"
    tool_lib="$2"
    std_lib="$3"
    sysroot_lib="$4"
    llvm_lib="$5"
    homebrew_lib="$6"
    shift 6

    # A cdylib (trust-mc-backend's librustc_codegen_trust_mc) is dlopened by the
    # compiler whose driver is already loaded. It must carry no rpath, or dyld
    # could resolve @rpath/librustc_driver-* to a second copy, and it takes no
    # -Cprefer-dynamic. It needs only the overlay's metadata closure.
    if is_cdylib "$@"; then
        exec "$RUSTC" --sysroot "$overlay" -L "$tool_lib" -L "$sysroot_lib" "$@"
    fi

    if [ -n "$llvm_lib" ] && [ -n "$homebrew_lib" ]; then
        exec "$RUSTC" \
            --sysroot "$overlay" \
            -Cprefer-dynamic \
            -L "$tool_lib" -L "$sysroot_lib" -L "$llvm_lib" -L "$homebrew_lib" \
            -Clink-arg=-Wl,-rpath,"$tool_lib" \
            -Clink-arg=-Wl,-rpath,"$std_lib" \
            -Clink-arg=-Wl,-rpath,"$sysroot_lib" \
            -Clink-arg=-Wl,-rpath,"$llvm_lib" \
            -Clink-arg=-Wl,-rpath,"$homebrew_lib" \
            "$@"
    elif [ -n "$llvm_lib" ]; then
        exec "$RUSTC" \
            --sysroot "$overlay" \
            -Cprefer-dynamic \
            -L "$tool_lib" -L "$sysroot_lib" -L "$llvm_lib" \
            -Clink-arg=-Wl,-rpath,"$tool_lib" \
            -Clink-arg=-Wl,-rpath,"$std_lib" \
            -Clink-arg=-Wl,-rpath,"$sysroot_lib" \
            -Clink-arg=-Wl,-rpath,"$llvm_lib" \
            "$@"
    else
        exec "$RUSTC" \
            --sysroot "$overlay" \
            -Cprefer-dynamic \
            -L "$tool_lib" -L "$sysroot_lib" \
            -Clink-arg=-Wl,-rpath,"$tool_lib" \
            -Clink-arg=-Wl,-rpath,"$std_lib" \
            -Clink-arg=-Wl,-rpath,"$sysroot_lib" \
            "$@"
    fi
}

sysroot="$active_sysroot"
target_libdir="$("$RUSTC" --print target-libdir)"
triple="$(basename "$(dirname "$target_libdir")")"
sysroot_lib="$sysroot/lib"

case "$(uname -s)" in
    Darwin) driver_suffix="dylib" ;;
    Linux) driver_suffix="so" ;;
    *)
        echo "trustc-private-wrapper: unsupported host $(uname -s)" >&2
        exit 1
        ;;
esac

# Prefer the dylib/so named by the compiler executable itself.  A sysroot may
# retain an older driver beside the active one during an atomic promotion.
driver_name=""
if command -v otool >/dev/null 2>&1; then
    driver_name="$(otool -L "$RUSTC" 2>/dev/null \
        | sed -n -E "s#.*(librustc_driver-[0-9a-f]+\\.$driver_suffix).*#\\1#p" \
        | head -1)"
elif command -v ldd >/dev/null 2>&1; then
    driver_name="$(ldd "$RUSTC" 2>/dev/null \
        | sed -n -E "s#.*(librustc_driver-[0-9a-f]+\\.$driver_suffix).*#\\1#p" \
        | head -1)"
fi
if [ -n "$driver_name" ] && [ -e "$sysroot_lib/$driver_name" ]; then
    driver="$sysroot_lib/$driver_name"
else
    driver="$(find "$sysroot_lib" -maxdepth 1 -type f \
        -name "librustc_driver-*.$driver_suffix" 2>/dev/null \
        | LC_ALL=C sort | head -1)"
fi
if [ -z "${driver:-}" ]; then
    echo "trustc-private-wrapper: no librustc_driver.$driver_suffix under $sysroot_lib" >&2
    exit 1
fi
hash="$(basename "$driver" \
    | sed -E "s/^librustc_driver-([0-9a-f]+)\\.$driver_suffix$/\\1/")"
case "$hash" in
    ''|*[!0-9a-f]*)
        echo "trustc-private-wrapper: cannot parse rustc_driver hash from $driver" >&2
        exit 1
        ;;
esac

# Only the roots TRUST_PRIVATE_SYSROOTS names (colon-separated, non-empty to
# reach this point) are searched.  Nothing is discovered on the caller's
# behalf: a bootstrap rustc-private-sysroots directory beside or inside the
# sysroot, or one in a sibling Trust checkout, is used only when the caller
# names it, so a configured root without a match fails closed instead of
# quietly borrowing another snapshot.
private_roots="$TRUST_PRIVATE_SYSROOTS"

tool_driver=""
old_ifs="$IFS"
IFS=:
for private_root in $private_roots; do
    [ -d "$private_root" ] || continue
    tool_driver="$(find "$private_root" -type f \
        -path "*/$triple/librustc_driver-$hash.$driver_suffix" 2>/dev/null \
        | LC_ALL=C sort | head -1)"
    [ -z "$tool_driver" ] || break
done
IFS="$old_ifs"
if [ -z "$tool_driver" ]; then
    echo "trustc-private-wrapper: no rustc-private-tool sysroot matches active driver hash $hash" >&2
    echo "trustc-private-wrapper: searched $private_roots" >&2
    echo "trustc-private-wrapper: set TRUST_PRIVATE_SYSROOTS to the matching bootstrap directory" >&2
    exit 1
fi

tool_lib="$(dirname "$tool_driver")"
tool_root="$(dirname "$tool_lib")"
tool_host="$tool_root/host"
std_lib="$target_libdir"

llvm_lib=""
homebrew_lib=""
if command -v brew >/dev/null 2>&1; then
    llvm_lib="$(brew --prefix llvm 2>/dev/null || true)/lib"
    homebrew_lib="$(brew --prefix 2>/dev/null || true)/lib"
    [ -d "$llvm_lib" ] || llvm_lib=""
    [ -d "$homebrew_lib" ] || homebrew_lib=""
fi

# The target directory is writable build state. Never source data from it, and
# constrain recursive cleanup to one canonical, hash-named child. Resolving the
# parent first also makes paths containing spaces safe without eval/word-split
# reconstruction. A root target directory is rejected as unnecessarily broad.
mkdir -p "$CACHE_ROOT"
cache_root="$(CDPATH='' cd -- "$CACHE_ROOT" && pwd -P)"
if [ -z "$cache_root" ] || [ "$cache_root" = "/" ]; then
    echo "trustc-private-wrapper: unsafe CARGO_TARGET_DIR for private overlay: ${cache_root:-<empty>}" >&2
    exit 1
fi
overlay_name="trust-private-sysroot-$hash"
overlay="$cache_root/$overlay_name"
if [ "$(dirname -- "$overlay")" != "$cache_root" ] \
    || [ "$(basename -- "$overlay")" != "$overlay_name" ]; then
    echo "trustc-private-wrapper: refusing unsafe private overlay target: $overlay" >&2
    exit 1
fi
if [ ! -e "$overlay/.ready" ]; then
    rm -rf -- "$overlay"
    mkdir -p "$overlay/lib/rustlib/$triple/lib"
    ln -sf "$sysroot/lib/rustlib/$triple/lib/"* \
        "$overlay/lib/rustlib/$triple/lib/" 2>/dev/null || true
    ln -sf "$tool_lib/"* "$overlay/lib/rustlib/$triple/lib/" 2>/dev/null || true
    if [ -d "$tool_host" ]; then
        ln -sf "$tool_host/"* "$overlay/lib/rustlib/$triple/lib/" 2>/dev/null || true
    fi
    touch "$overlay/.ready"
fi

emit_and_exec \
    "$overlay" "$tool_lib" "$std_lib" "$sysroot_lib" \
    "$llvm_lib" "$homebrew_lib" "$@"
