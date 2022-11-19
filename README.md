# LaxCow

Clone-on-write smart pointer similar to [Cow](https://doc.rust-lang.org/std/borrow/enum.Cow.html), but with relaxed trait constraints.

# Examples

## Simple usage

```rust
use laxcow::LaxCow;

let lc = LaxCow::Borrowed("foobar");

let lc2 = lc.clone();
assert_eq!(lc2, LaxCow::Borrowed("foobar"));

let owned = lc.into_owned();
assert_eq!(owned, "foobar".to_owned());
```

## Usage not possible with `Cow`

Storing a borrowed struct which doesn't implement [`Clone`](https://doc.rust-lang.org/std/clone/trait.Clone.html).
This is possible because `LaxCow::Owned` variant is not restricted
by the `LaxCow::Borrowed` variant via [`ToOwned`](https://doc.rust-lang.org/std/borrow/trait.ToOwned.html) trait.

```rust
use laxcow::LaxCow;

struct Foo;

let laxcow = LaxCow::<_, ()>::Borrowed(&Foo);
```

## `Cow` definition by wrapping `LaxCow`

```rust
use laxcow::LaxCow;

struct Cow<'a, T: ?Sized + ToOwned>(LaxCow::<'a, T, T::Owned>);
```
