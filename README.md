# ![logo](https://raw.githubusercontent.com/safer-rust/RAPx/main/logo.png)
RAPx (Rust Analysis Platform with Extensions) [![license: MPL 2.0](https://img.shields.io/badge/license-MPL%202.0-brightgreen)](./LICENSE-MPL)[![docs.rs](https://img.shields.io/badge/docs-docs.rs-blue)](https://docs.rs/rapx) is an advanced static analysis platform for Rust. It provides an extensible framework for building and integrating powerful analysis capabilities that go beyond those available in the standard rustc compiler, empowering developers to reason about safety, robustness, and performance at a deeper level.

RAPx is available on crates.io. [![crates.io](https://img.shields.io/badge/crates.io-latest-orange)](https://crates.io/crates/rapx)

## Features
# ![logo](https://raw.githubusercontent.com/safer-rust/RAPx/main/feature.png)
RAPx is structured into two layers: a core layer offering essential program analysis algorithms (e.g., alias and dataflow analysis), and an application layer implementing specific tasks such as bug detection. This separation of concerns promotes modular development and fosters collaboration between algorithm and application developers.

The project is still under heavy development. For further details, please refer to the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/).

## Quick Start

Install `nightly-2026-04-03` on which rapx is compiled with. This just needs to do once on your machine. If the toolchain exists,
this will do nothing.

```shell
rustup toolchain install nightly-2026-04-03 --profile minimal --component rustc-dev,rust-src,llvm-tools-preview
cargo +nightly-2026-04-03 install rapx --git https://github.com/safer-rust/RAPx.git
```

## Usage

Navigate to your Rust project folder containing a `Cargo.toml` file. Then run `rapx` by manually specifying the toolchain version according to the [toolchain override shorthand syntax](https://rust-lang.github.io/rustup/overrides.html#toolchain-override-shorthand).

```shell
cargo +nightly-2026-04-03 rapx [rapx options] -- [cargo check options]
```

or by setting up default toolchain to the required version.
```shell
rustup default nightly-2026-04-03
```

Check out supported options with `-help`:

```shell
$ cargo rapx --help

Usage: cargo rapx [OPTIONS] <COMMAND> [-- [CARGO_FLAGS]]

Commands:
  analyze  perform various analyses on the crate, e.g., alias analysis, callgraph generation
  check    check potential vulnerabilities in the crate, e.g., use-after-free, memory leak
  verify   verify annotated functions in the crate, e.g., identify #[rapx::verify] targets
  help     Print this message or the help of the given subcommand(s)

Options:
      --timeout <TIMEOUT>        specify the timeout seconds in running rapx
      --test-crate <TEST_CRATE>  specify the tested package in the workspace
  -h, --help                     Print help
  -V, --version                  Print version

NOTE: multiple detections can be processed in single run by 
appending the options to the arguments. Like `cargo rapx check -f -m`
will perform two kinds of detection in a row.

Examples:

  1. detect use-after-free and memory leak:
     cargo rapx check -f -m
  2. detect optimization opportunities:
     cargo rapx check -o report
  3. perform alias analysis:
     cargo rapx analyze alias
  4. verify annotated functions:
     cargo rapx verify --prepare-targets
```

### `analyze` command

```
Usage: cargo rapx analyze <COMMAND>

Commands:
  alias       alias analysis (meet-over-paths by default)
  adg         API dependency graphs
  callgraph   callgraph generation
  deadlock    lock dependency analysis and deadlock detection
  dataflow    dataflow graphs
  owned-heap  analyze heap-owning types
  paths       path-sensitive CFG paths
  range       range analysis
  scan        basic crate info
  mir         print MIR
  dot-mir     print MIR as DOT
  help        Print this message or the help of the given subcommand(s)

Options:
  -h, --help  Print help
```

### `check` command

```
Usage: cargo rapx check [OPTIONS]

Options:
  -f, --uaf [<UAF>]    detect use-after-free/double-free (optional level, default 1)
  -m, --mleak          detect memory leakage
  -o, --opt [<OPT>]    automatically detect code optimization chances
                       [possible values: report, default, all]
  -h, --help           Print help
```

### `verify` command

The `verify` command provides a contract-based verification pipeline for functions annotated with `#[rapx::verify]`. It uses path-sensitive backward/forward analysis and Z3-based SMT solving to prove safety properties.

```
Usage: cargo rapx verify [OPTIONS]

Options:
      --prepare-targets            identify #[rapx::verify] functions and list their safety contracts
      --allow-pathseg-repeat <N>  number of extra SCC postfix repetitions during path enumeration (default 0)
      --mode <MODE>               verification mode: scan, targeted, invless (default scan)
  -h, --help                      Print help
```

Verification modes:
- `scan` — auto-detect: verify all functions with unsafe callees or struct invariants
- `targeted` — only verify functions annotated with `#[rapx::verify]`
- `invless` — verify without struct invariants as pre/post-conditions, deriving safety requirements automatically from the safety flow graph

```rust
#![feature(register_tool)]
#![register_tool(rapx)]

#[rapx::verify]
fn init_buffer(buf: *mut u32, len: usize) {
    unsafe {
        // rapx checks: NonNull(buf), Align(buf, u32), InBound(buf, len)
        core::ptr::write(buf.add(len - 1), 0);
    }
}

#[rapx::requires(NonNull(_ptr))]
unsafe fn custom_ptr_op(_ptr: *const i32) -> i32 {
    unsafe { *_ptr }
}
```

Safety properties include: `Align`, `NonNull`, `Allocated`, `InBound`, `Init`, `ValidPtr`, `Deref`, `Ptr2Ref`, and more. See the [RAPx-Book](https://safer-rust.github.io/RAPx-Book/) for the full list.

### Verification Property Support Checklist

This checklist maps RAPx's contract verification to the [Primitive Safety Properties](https://github.com/safer-rust/safety-tags/blob/main/primitive-sp.md) defined in `safer-rust/safety-tags`.

| Primitive SP                 | RAPx tag       | Supported |
|------------------------------|----------------|:---------:|
| Align(p, T)                  | `Align`        |     ✅    |
| Size(T, c)                   | `Size`         |     —     |
| !Padding(T)                  | `NoPadding`    |     —     |
| !Null(p)                     | `NonNull`      |     ✅    |
| Allocated(p, T, len, A)      | `Allocated`    |     —     |
| InBound(p, T, len)           | `InBound`      |     ✅    |
| !Overlap(dst, src, T, len)   | `NonOverlap`   |     —     |
| ValidNum(exp, vrange)        | `ValidNum`     |     —     |
| ValidString(arange)          | `ValidString`  |     —     |
| ValidCStr(p, len)            | `ValidCStr`    |     —     |
| Init(p, T, len)              | `Init`         |     —     |
| Unwrap(x, T)                 | `Unwrap`       |     —     |
| Typed(p, T)                  | `Typed`        |     —     |
| !Owned(p)                    | `Owning`       |     —     |
| Alias(p1, p2)                | `Alias`        |     —     |
| Alive(p, l)                  | `Alive`        |     —     |
| Pinned(p, l)                 | `Pinned`       |     —     |
| !Volatile(p, T, len)         | `NonVolatile`  |     —     |
| Opened(fd)                   | `Opened`       |     —     |
| Trait(T, trait)              | `Trait`        |     —     |
| !Reachable()                 | `Unreachable`  |     —     |
| ValidPtr(p, T, len)           | `ValidPtr`     |     —     |
| Deref(p, T, len)              | `Deref`        |     —     |
| Ptr2Ref(p, T)                 | `Ptr2Ref`      |     —     |
| Layout(p, layout)             | `Layout`       |     —     |

### `deadlock` analysis

The `deadlock` command performs tag-driven lock dependency analysis to detect potential deadlocks in a crate. It integrates into the `rustc` compilation pipeline and uses MIR dataflow analysis for precise reasoning about lock acquisition order and interrupt context.

Deadlock detection is **crate-local**: it builds the lock dependency graph within the current crate. Cross-crate analysis is supported via tag serialization with `--save-tags` / `--load-tags`.

#### Tag System

To use deadlock detection, annotate the target codebase with `#[rapx::...]` tool attributes. Each crate that uses these tags must enable:

```rust
#![feature(register_tool)]
#![register_tool(rapx)]
```

##### `#[rapx::LockType(Name = "...")]`

Marks a struct as a lock type. Place on the struct definition.

```rust
#[rapx::LockType(Name = "SpinLock")]
pub struct SpinLock<T: ?Sized, G = PreemptDisabled> { /* ... */ }
```

| Parameter | Description |
|-----------|-------------|
| `Name` | Human-readable name for the lock type |

##### `#[rapx::LockGuardType(Name = "...")]`

Marks a struct as a lock guard — the RAII guard returned by `lock()` calls.

```rust
#[rapx::LockGuardType(Name = "SpinLockGuard")]
pub struct SpinLockGuard<'a, T: ?Sized, G: SpinGuardian> { /* ... */ }
```

##### `#[rapx::LockOp(LockArg = N, GuardIrqDisabled = BOOL)]`

Marks a method as a lock acquisition API. Place on the `fn` definition.

```rust
#[rapx::LockOp(LockArg = 0, GuardIrqDisabled = false)]
pub fn lock(&self) -> MutexGuard<'_, T> { /* ... */ }
```

| Parameter | Description |
|-----------|-------------|
| `LockArg` | Index of the `self` parameter's field that holds the lock (usually `0`) |
| `GuardIrqDisabled` | Whether holding the returned guard disables local interrupts |

If a lock's `lock()` method omits `#[rapx::LockOp]`, RAPx falls back to legacy heuristics and emits a warning.

##### `#[rapx::IntrApi(Type = Enable|Disable, Nested = BOOL)]`

Marks a function as an interrupt enable/disable API, used by the ISR analyzer to track interrupt state at each program point.

```rust
#[rapx::IntrApi(Type = Disable, Nested = true)]
pub fn disable_local() -> DisabledLocalIrqGuard { /* ... */ }
```

| Parameter | Description |
|-----------|-------------|
| `Type` | `Enable` or `Disable` |
| `Nested` | Whether the API supports nested calls |

##### `#[rapx::IsrEntry]`

Marks a function as an interrupt service routine entry point. RAPx recursively traces the call graph from all ISR entries to build the ISR function set, which is used to detect interrupt preemption edges in the lock dependency graph.

```rust
#[rapx::IsrEntry]
pub(crate) unsafe fn do_inter_processor_call(_trapframe: &TrapFrame) { /* ... */ }
```

#### CLI Usage

```
Usage: cargo rapx analyze deadlock [OPTIONS] [-- [CARGO_FLAGS]]
```

| Option | Description |
|--------|-------------|
| `--save-tags <PATH>` | Save resolved tags to a JSON file for downstream crates |
| `--load-tags <PATH>` | Load tags from a JSON file produced by `--save-tags` |

**Examples:**

```bash
# Basic analysis within the current crate
cargo rapx analyze deadlock

# Specify target architecture (required for no_std crates)
cargo rapx analyze deadlock -- --target x86_64-unknown-none

# Analyze all workspace members
cargo rapx analyze deadlock -- --workspace

# Save tags for downstream crate analysis
cargo rapx analyze deadlock --save-tags ./ostd_tags.json -- --target x86_64-unknown-none

# Load upstream tags and analyze the current crate
cargo rapx analyze deadlock --load-tags ./ostd_tags.json -- --target x86_64-unknown-none

# Enable verbose logging
RAP_LOG=debug cargo rapx analyze deadlock -- --target x86_64-unknown-none
```

#### Interrupt-Aware Analysis

Deadlock detection is interrupt-aware: by tagging ISR entry points (`#[rapx::IsrEntry]`) and interrupt control APIs (`#[rapx::IntrApi]`), RAPx tracks which locks are held with interrupts disabled and detects cases where the same lock is acquired in both normal and interrupt context — a common source of deadlocks in OS kernels.

#### Analysis Pipeline

The deadlock detector runs through six phases:

1. **Callgraph construction** — build the inter-procedural call graph
2. **Tag parsing** — collect `#[rapx::...]` attributes from the crate
3. **Lock information collection** — identify lock types, instances, guards; build lock maps via iterative MIR dataflow
4. **Lockset analysis** — compute held-lock sets at each program point (CFG fixed-point iteration)
5. **Interrupt state analysis** — track IRQ state and identify ISR call chains
6. **Dependency graph & reporting** — construct the lock dependency graph and detect deadlock cycles

The dependency graph edge direction is **new lock → old lock** (acquiring a new lock while already holding an old lock). Two edge types exist:
- **Normal edges** — locks held simultaneously in the same execution context
- **Interrupt edges** — a lock held in normal context is also acquired within an ISR, indicating a potential interrupt preemption deadlock

### Environment Variables (values are case insensitive)

| var             | default when absent | possible values     | description                  |
|-----------------|---------------------|---------------------|------------------------------|
| `RAPX_LOG`       | info                | trace, debug, info, warn | verbosity of logging   |
| `RAPX_CLEAN`     | true                | true, false         | run cargo clean before check |
| `RAPX_RECURSIVE` | none                | none, shallow, deep | scope of packages to check   |
| `RAPXFLAGS`      | (unset)             | CLI arguments       | arguments passed to `rapx` binary directly |

For `RAPX_RECURSIVE`:
* `none`: check for current folder
* `shallow`: check for current workspace members
* `deep`: check for all workspaces from current folder

NOTE: for `shallow` or `deep`, rapx will enter each member folder to do the check.

If RAPx gets stuck after executing `cargo clean`, try manually downloading metadata dependencies by running `cargo metadata`.

