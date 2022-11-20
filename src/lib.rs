//! Library provides [`LaxCow`] clone-on-write smart pointer with relaxed
//! trait constraints relative to [`Cow`]. The main difference being, [`LaxCow`]
//! is usable even if the owned type is not equal to the target type of
//! borrow type's implementation of [`ToOwned`] trait.
//!
//! Crate is totally `no_std`.

#![no_std]

extern crate alloc;

use alloc::borrow::{Cow, ToOwned};
use core::{
    borrow::Borrow,
    cmp::Ordering,
    fmt::{Debug, Display},
    hash::{Hash, Hasher},
    ops::Deref,
};

/// Clone-on-write smart pointer with relaxed trait constraints
/// relative to [`Cow`].
///
/// [`LaxCow`] does not constrain owned type in its type definition, but in
/// methods that specifically require this. Thus, Owned type is generic and
/// may need to be explicitly defined when instantiating. Also, [`LaxCow`]
/// isn't strictly clone-on-write as not all instances of it support
/// writing i.e. mutable access.
///
/// # Examples
///
/// ## Simple usage
///
/// ```
/// use laxcow::LaxCow;
///
/// let lc = LaxCow::Borrowed("foobar");
///
/// let lc2 = lc.clone();
/// assert_eq!(lc2, LaxCow::<_, String>::Borrowed("foobar"));
///
/// let owned = lc.into_owned();
/// assert_eq!(owned, "foobar".to_owned());
/// ```
///
/// ## Usage not possible with [`Cow`]
///
/// Storing a borrowed struct which doesn't implement `Clone`.
/// This is possible because [`LaxCow::Owned`] variant is not restricted
/// by the [`LaxCow::Borrowed`] variant via [`ToOwned`] trait.
///
/// ```
/// use laxcow::LaxCow;
///
/// struct Foo;
///
/// let laxcow = LaxCow::<_, ()>::Borrowed(&Foo);
/// ```
///
/// ## [`Cow`] definition by wrapping [`LaxCow`]
///
/// ```
/// use laxcow::LaxCow;
///
/// struct Cow<'a, T: ?Sized + ToOwned>(LaxCow::<'a, T, T::Owned>);
/// ```
pub enum LaxCow<'a, B: ?Sized, O = B> {
    Borrowed(&'a B),
    Owned(O),
}

impl<B: ?Sized, O> LaxCow<'_, B, O> {
    /// Returns `true` if [`LaxCow`] contains borrowed item, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use laxcow::LaxCow;
    ///
    /// // We don't care what owned type is as it is not used.
    /// let borrowed = LaxCow::<i32, ()>::Borrowed(&42);
    ///
    /// assert!(borrowed.is_borrowed());
    /// ```
    pub const fn is_borrowed(&self) -> bool {
        match self {
            Self::Borrowed(_) => true,
            Self::Owned(_) => false,
        }
    }

    /// Returns `true` if [`LaxCow`] contains owned item, `false` otherwise.
    ///
    /// # Examples
    /// ```
    /// use laxcow::LaxCow;
    ///
    /// // We don't care what borrowed type is as it is not used.
    /// let owned = LaxCow::<(), i32>::Owned(42);
    ///
    /// assert!(owned.is_owned());
    /// ```
    pub const fn is_owned(&self) -> bool {
        !self.is_borrowed()
    }

    /// Returns mutable reference to the owned item.
    ///
    /// If the item is currently borrowed, it will converted
    /// into owned via [`ToOwned`] trait before returning mutable
    /// reference to it.
    ///
    /// # Examples
    /// ```
    /// use laxcow::LaxCow;
    ///
    /// let mut borrowed = LaxCow::Borrowed(&42);
    /// let mut owned = LaxCow::<i32, _>::Owned(42);
    ///
    /// *borrowed.to_mut() += 10;
    /// *owned.to_mut() += 10;
    ///
    /// assert_eq!(borrowed, LaxCow::Owned(52));
    /// assert_eq!(owned, LaxCow::Owned(52));
    /// ```
    pub fn to_mut(&mut self) -> &mut O
    where
        B: ToOwned<Owned = O>,
    {
        match self {
            Self::Borrowed(borrowed) => {
                *self = Self::Owned(borrowed.to_owned());
                match self {
                    Self::Owned(owned) => owned,
                    Self::Borrowed(_) => unreachable!(),
                }
            }
            Self::Owned(owned) => owned,
        }
    }

    /// Returns mutable reference to the owned item wrapped in [`Some`] if the item is owned.
    /// Otherwise, if the item is borrowed, [`None`] will be returned.
    ///
    /// # Examples
    /// ```
    /// use laxcow::LaxCow;
    ///
    /// let mut borrowed = LaxCow::<_, String>::Borrowed("foobar");
    /// let mut owned = LaxCow::<str, _>::Owned("foobar".to_owned());
    ///
    /// assert_eq!(borrowed.as_owned_mut(), None);
    /// assert_eq!(owned.as_owned_mut(), Some(&mut "foobar".to_owned()));
    /// ```
    pub fn as_owned_mut(&mut self) -> Option<&mut O> {
        match self {
            Self::Borrowed(_) => None,
            Self::Owned(owned) => Some(owned),
        }
    }

    /// Consumes [`LaxCow`] and returns owned item as is, or borrowed
    /// item via [`ToOwned`] trait conversion.
    ///
    /// # Examples
    /// ```
    /// use laxcow::LaxCow;
    ///
    /// let borrowed: LaxCow<_, String> = LaxCow::Borrowed("foobar");
    /// let owned: LaxCow<str, _> = LaxCow::Owned("foobar".to_owned());
    ///
    /// assert_eq!(borrowed.into_owned(), "foobar".to_owned());
    /// assert_eq!(owned.into_owned(), "foobar".to_owned());
    /// ```
    pub fn into_owned(self) -> O
    where
        B: ToOwned<Owned = O>,
    {
        match self {
            Self::Borrowed(borrowed) => borrowed.to_owned(),
            Self::Owned(owned) => owned,
        }
    }

    /// Returns owned item wrapped in [`Some`], or [`None`] if the item is borrowed.
    ///
    /// # Examples
    /// ```
    /// use laxcow::LaxCow;
    ///
    /// let mut borrowed = LaxCow::<_, String>::Borrowed("foobar");
    /// let mut owned = LaxCow::<str, _>::Owned("foobar".to_owned());
    ///
    /// assert_eq!(borrowed.try_into_owned(), None);
    /// assert_eq!(owned.try_into_owned(), Some("foobar".to_owned()));
    /// ```
    pub fn try_into_owned(self) -> Option<O> {
        match self {
            Self::Borrowed(_) => None,
            Self::Owned(owned) => Some(owned),
        }
    }
}

impl<B: ?Sized, O> AsRef<B> for LaxCow<'_, B, O>
where
    O: AsRef<B>,
{
    fn as_ref(&self) -> &B {
        match self {
            Self::Borrowed(borrowed) => borrowed,
            Self::Owned(owned) => owned.as_ref(),
        }
    }
}

impl<B: ?Sized, O> Clone for LaxCow<'_, B, O>
where
    O: Clone,
{
    fn clone(&self) -> Self {
        match self {
            Self::Borrowed(borrowed) => Self::Borrowed(borrowed),
            Self::Owned(owned) => Self::Owned(owned.clone()),
        }
    }
}

impl<B: ?Sized, O> Debug for LaxCow<'_, B, O>
where
    B: Debug,
    O: Debug,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Borrowed(borrowed) => Debug::fmt(borrowed, f),
            Self::Owned(owned) => Debug::fmt(owned, f),
        }
    }
}

impl<B: ?Sized, O> Default for LaxCow<'_, B, O>
where
    O: Default,
{
    fn default() -> Self {
        Self::Owned(Default::default())
    }
}

impl<B: ?Sized, O> Deref for LaxCow<'_, B, O>
where
    O: Borrow<B>,
{
    type Target = B;

    fn deref(&self) -> &B {
        match self {
            Self::Borrowed(borrowed) => borrowed,
            Self::Owned(owned) => owned.borrow(),
        }
    }
}

impl<B: ?Sized, O> Display for LaxCow<'_, B, O>
where
    B: Display,
    O: Display,
{
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Borrowed(borrowed) => Display::fmt(borrowed, f),
            Self::Owned(owned) => Display::fmt(owned, f),
        }
    }
}

impl<'a, B: ?Sized, O> From<Cow<'a, B>> for LaxCow<'a, B, O>
where
    B: ToOwned<Owned = O>,
{
    fn from(cow: Cow<'a, B>) -> Self {
        match cow {
            Cow::Borrowed(borrowed) => LaxCow::Borrowed(borrowed),
            Cow::Owned(owned) => LaxCow::Owned(owned),
        }
    }
}

impl<'a, B: ?Sized, O> From<LaxCow<'a, B, O>> for Cow<'a, B>
where
    B: ToOwned<Owned = O>,
{
    fn from(laxcow: LaxCow<'a, B, O>) -> Self {
        match laxcow {
            LaxCow::Borrowed(borrowed) => Cow::Borrowed(borrowed),
            LaxCow::Owned(owned) => Cow::Owned(owned),
        }
    }
}

impl<B: ?Sized, O> Hash for LaxCow<'_, B, O>
where
    O: Borrow<B>,
    B: Hash,
{
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        Hash::hash(&**self, state)
    }
}

impl<B: ?Sized, O> Eq for LaxCow<'_, B, O>
where
    B: Eq,
    O: Borrow<B>,
{
}

impl<B: ?Sized, O> Ord for LaxCow<'_, B, O>
where
    O: Borrow<B>,
    B: Ord,
{
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        Ord::cmp(&**self, &**other)
    }
}

impl<'a, 'b, B: ?Sized, O, B2: ?Sized, O2> PartialEq<LaxCow<'a, B2, O2>> for LaxCow<'b, B, O>
where
    B: PartialEq<B2>,
    O: Borrow<B>,
    O2: Borrow<B2>,
{
    #[inline]
    fn eq(&self, other: &LaxCow<'a, B2, O2>) -> bool {
        PartialEq::eq(&**self, &**other)
    }
}

impl<B: ?Sized, O> PartialOrd for LaxCow<'_, B, O>
where
    B: PartialOrd,
    O: Borrow<B>,
{
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        PartialOrd::partial_cmp(&**self, &**other)
    }
}

#[cfg(test)]
mod tests {
    extern crate std;

    use alloc::{format, string::String};
    use std::collections::hash_map::DefaultHasher;

    use super::*;

    #[test]
    fn send_sync() {
        fn foobar(_: impl Send + Sync) {}

        let laxcow = LaxCow::<i32>::Borrowed(&42);
        foobar(laxcow);
    }

    #[test]
    fn debug() {
        let laxcow: LaxCow<str, ()> = LaxCow::Borrowed("foobar");
        assert_eq!(format!("{laxcow:?}"), "\"foobar\"");

        let laxcow: LaxCow<(), String> = LaxCow::Owned("foobar".to_owned());
        assert_eq!(format!("{laxcow:?}"), "\"foobar\"");
    }

    #[test]
    fn display() {
        let laxcow: LaxCow<str, String> = LaxCow::Borrowed("foobar");
        assert_eq!(format!("{laxcow:?}"), "\"foobar\"");

        let laxcow: LaxCow<str, String> = LaxCow::Owned("foobar".to_owned());
        assert_eq!(format!("{laxcow:?}"), "\"foobar\"");
    }

    #[test]
    fn clone() {
        let cow: LaxCow<_, String> = LaxCow::Borrowed("foobar");
        assert_eq!(cow.clone(), LaxCow::<_, String>::Borrowed("foobar"));

        let cow: LaxCow<str, _> = LaxCow::Owned("foobar".to_owned());
        assert_eq!(cow.clone(), LaxCow::<str, _>::Owned("foobar".to_owned()));
    }

    #[test]
    fn as_ref() {
        let cow: LaxCow<_, String> = LaxCow::Borrowed("foobar");
        assert_eq!(cow.as_ref(), "foobar");

        let cow: LaxCow<str, _> = LaxCow::Owned("foobar".to_owned());
        assert_eq!(cow.as_ref(), "foobar");
    }

    #[test]
    fn default() {
        let cow = LaxCow::<str, String>::default();
        assert_eq!(cow, LaxCow::<str, String>::Owned(Default::default()));
    }

    #[test]
    fn deref() {
        let cow = LaxCow::<_, String>::Borrowed("foobar");
        assert_eq!(cow.deref(), "foobar");

        let cow = LaxCow::<str, _>::Owned("foobar".to_owned());
        assert_eq!(cow.deref(), "foobar");
    }

    #[test]
    fn from_cow_into_laxcow() {
        let cow = Cow::Borrowed("foobar");
        let laxcow = LaxCow::from(cow);
        assert_eq!(laxcow, LaxCow::<_, String>::Borrowed("foobar"));

        let cow: Cow<str> = Cow::Owned("foobar".to_owned());
        let laxcow = LaxCow::from(cow);
        assert_eq!(laxcow, LaxCow::<str, _>::Owned("foobar".to_owned()));
    }

    #[test]
    fn into_cow_from_laxcow() {
        let laxcow = LaxCow::Borrowed("foobar");
        let cow = Cow::from(laxcow);
        assert_eq!(cow, Cow::Borrowed("foobar"));

        let laxcow = LaxCow::Owned("foobar".to_owned());
        let cow: Cow<str> = Cow::from(laxcow);
        assert_eq!(cow, Cow::<str>::Owned("foobar".to_owned()));
    }

    #[test]
    fn eq() {
        let borrowed: LaxCow<_, String> = LaxCow::Borrowed("foobar");
        let owned: LaxCow<str, _> = LaxCow::Owned("foobar".to_owned());

        assert_eq!(borrowed, owned);

        let borrowed: LaxCow<i32> = LaxCow::Borrowed(&42);
        let owned = LaxCow::Owned(42);

        assert_eq!(borrowed, owned);
    }

    #[test]
    fn ord() {
        let borrowed: LaxCow<i32> = LaxCow::Borrowed(&42);
        let owned = LaxCow::Owned(100);
        assert_eq!(borrowed.cmp(&owned), Ordering::Less);

        let borrowed: LaxCow<i32> = LaxCow::Borrowed(&42);
        let owned = LaxCow::Owned(42);
        assert_eq!(borrowed.cmp(&owned), Ordering::Equal);

        let borrowed: LaxCow<i32> = LaxCow::Borrowed(&42);
        let owned = LaxCow::Owned(1);
        assert_eq!(borrowed.cmp(&owned), Ordering::Greater);
    }

    #[test]
    fn hash() {
        let borrowed: LaxCow<_, String> = LaxCow::Borrowed("foobar");
        let owned: LaxCow<str, _> = LaxCow::Owned("foobar".to_owned());

        fn hash_helper(h: impl Hash) -> u64 {
            let mut hasher = DefaultHasher::new();
            h.hash(&mut hasher);
            hasher.finish()
        }

        assert_eq!(borrowed, owned);
        assert_eq!(hash_helper(borrowed), hash_helper(owned));
    }
}
