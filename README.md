# LaxCow

[![CI status](https://github.com/kauppie/laxcow/actions/workflows/rust.yml/badge.svg?branch=main)](https://github.com/kauppie/laxcow/actions/workflows/rust.yml)
[![License: Apache](https://img.shields.io/badge/License-Apache_2.0-red.svg)](https://opensource.org/licenses/Apache-2.0)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](https://opensource.org/licenses/MIT)

Clone-on-write smart pointer similar to [Cow](https://doc.rust-lang.org/std/borrow/enum.Cow.html), but with relaxed trait constraints. Crate is totally `no_std`.

## Examples

### Simple usage

```rust
use laxcow::LaxCow;

let lc = LaxCow::Borrowed("foobar");

let lc2 = lc.clone();
assert_eq!(lc2, LaxCow::Borrowed("foobar"));

let owned = lc.into_owned();
assert_eq!(owned, "foobar".to_owned());
```

### Usage not possible with `Cow`

Storing a borrowed struct which doesn't implement [`Clone`](https://doc.rust-lang.org/std/clone/trait.Clone.html).
This is possible because `LaxCow::Owned` variant is not restricted
by the `LaxCow::Borrowed` variant via [`ToOwned`](https://doc.rust-lang.org/std/borrow/trait.ToOwned.html) trait.

```rust
use laxcow::LaxCow;

struct Foo;

let laxcow = LaxCow::<_, ()>::Borrowed(&Foo);
```

### `Cow` definition by wrapping `LaxCow`

This example shows the difference between `LaxCow` and `Cow`. It makes `Cow` a struct, but only works here as an example.

```rust
use laxcow::LaxCow;

struct Cow<'a, T: ?Sized + ToOwned>(LaxCow::<'a, T, <T as ToOwned>::Owned>);
```

## License

Licensed under either of

- Apache License, Version 2.0
  ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
- MIT license
  ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
