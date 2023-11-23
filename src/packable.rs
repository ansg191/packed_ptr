use core::mem::MaybeUninit;

/// A type that can be packed into a pointer.
///
/// # Safety
///
/// This trait is unsafe because it has certain requirements that must be upheld by the implementor:
/// - `unpack(pack(x)) == x` for all `x`.
/// - `MAX_BITS` must be the maximum number of bits that are returned by `pack`.
/// - `pack` and `unpack` must be *infallible*.
pub unsafe trait Packable: Copy {
    /// The maximum number of bits of the output of `pack`.
    const MAX_BITS: usize = core::mem::size_of::<Self>() * 8;

    /// Packs a value into an integer.
    ///
    /// # Safety
    ///
    /// The value returned by this function must be entirely contained within the lower [`MAX_BITS`]
    /// bits of the returned integer. The remaining upper bits **MUST** be zero.
    ///
    /// [`MAX_BITS`]: Self::MAX_BITS
    fn pack(self) -> usize;

    /// Unpacks a value from an integer previously packed by [`pack`].
    ///
    /// # Safety
    ///
    /// `value` **MUST** have been previously returned by [`pack`]. Implementors can assume that
    /// this is the case.
    ///
    /// Implementors **MUST** ensure that the returned value is *identical* to the value that was
    /// passed to [`pack`]. In other words, `unpack(pack(x)) == x` for all `x`.
    ///
    /// [`pack`]: Self::pack
    unsafe fn unpack(value: usize) -> Self;
}

macro_rules! impl_int {
    ($($t:ty),*) => {
        $(
            unsafe impl Packable for $t {
                fn pack(self) -> usize {
                    self as usize
                }
                unsafe fn unpack(value: usize) -> Self {
                    value as $t
                }
            }
        )*
    };
}

impl_int!(u8, u16, u32, usize, i8, i16, i32, isize);
#[cfg(target_pointer_width = "64")]
impl_int!(u64, i64);

unsafe impl Packable for () {
    fn pack(self) -> usize {
        0
    }

    unsafe fn unpack(_: usize) -> Self {}
}

unsafe impl Packable for bool {
    const MAX_BITS: usize = 1;

    fn pack(self) -> usize {
        usize::from(self)
    }

    unsafe fn unpack(value: usize) -> Self {
        value != 0
    }
}

macro_rules! internal_tuple_unpack {
    ($value:ident, $t:ident) => {
        let $t = {
            let mask = (1 << <$t as Packable>::MAX_BITS) - 1;
            let $t = <$t as Packable>::unpack($value & mask);
            $value >>= <$t as Packable>::MAX_BITS;
            $t
        };
    };
    ($value:ident, $t:ident, $($rest:ident),*) => {
        internal_tuple_unpack!($value, $($rest),*);
        let $t = {
            let mask = (1 << <$t as Packable>::MAX_BITS) - 1;
            let $t = <$t as Packable>::unpack($value & mask);
            $value >>= <$t as Packable>::MAX_BITS;
            $t
        };
    };
}

macro_rules! impl_tuple {
    ($($t:ident),*) => {
        #[allow(non_snake_case)]
        unsafe impl<$($t: Packable),*> Packable for ($($t,)*) {
            const MAX_BITS: usize = 0 $(+ <$t as Packable>::MAX_BITS)*;
            fn pack(self) -> usize {
                let ($($t,)*) = self;
                let mut value = 0;
                $(
                    value <<= <$t as Packable>::MAX_BITS;
                    value |= <$t as Packable>::pack($t);
                )*
                value
            }
            #[allow(unused_assignments)]
            unsafe fn unpack(value: usize) -> Self {
                let mut value = value;
                internal_tuple_unpack!(value, $($t),*);
                ($($t,)*)
            }
        }
    };
}

impl_tuple!(T0);
impl_tuple!(T0, T1);
impl_tuple!(T0, T1, T2);
impl_tuple!(T0, T1, T2, T3);
impl_tuple!(T0, T1, T2, T3, T4);
impl_tuple!(T0, T1, T2, T3, T4, T5);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8);
impl_tuple!(T0, T1, T2, T3, T4, T5, T6, T7, T8, T9);

unsafe impl<T: Packable, const N: usize> Packable for [T; N] {
    const MAX_BITS: usize = T::MAX_BITS * N;

    fn pack(self) -> usize {
        self.into_iter()
            .fold(0, |acc, x| acc << T::MAX_BITS | x.pack())
    }

    unsafe fn unpack(mut value: usize) -> Self {
        let mask: usize = (1 << T::MAX_BITS) - 1;

        let mut array: MaybeUninit<[T; N]> = MaybeUninit::uninit();
        for i in 1..=N {
            let ptr = array.as_mut_ptr().cast::<T>();
            ptr.add(N - i).write(T::unpack(value & mask));
            value >>= T::MAX_BITS;
        }
        array.assume_init()
    }
}

unsafe impl<T: Packable> Packable for Option<T> {
    const MAX_BITS: usize = T::MAX_BITS + 1;

    fn pack(self) -> usize {
        self.map_or(0, |x| x.pack() << 1 | 1)
    }

    unsafe fn unpack(value: usize) -> Self {
        if value == 0 {
            None
        } else {
            Some(T::unpack(value >> 1))
        }
    }
}

unsafe impl<T: Packable, E: Packable> Packable for Result<T, E> {
    const MAX_BITS: usize = [T::MAX_BITS, E::MAX_BITS][(T::MAX_BITS < E::MAX_BITS) as usize] + 1;

    fn pack(self) -> usize {
        match self {
            Ok(x) => x.pack() << 1 | 1,
            Err(e) => e.pack() << 1,
        }
    }

    unsafe fn unpack(value: usize) -> Self {
        if value & 1 == 0 {
            Err(E::unpack(value >> 1))
        } else {
            Ok(T::unpack(value >> 1))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int() {
        assert_eq!(<u8 as Packable>::MAX_BITS, 8);
        assert_eq!(<u16 as Packable>::MAX_BITS, 16);
        assert_eq!(<u32 as Packable>::MAX_BITS, 32);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(<u64 as Packable>::MAX_BITS, 64);

        assert_eq!(0u8.pack(), 0);
        assert_eq!(255u8.pack(), 255);
        assert_eq!(0u16.pack(), 0);
        assert_eq!(65535u16.pack(), 65535);
        assert_eq!(0u32.pack(), 0);
        assert_eq!(4_294_967_295_u32.pack(), 4_294_967_295);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(0u64.pack(), 0);
        #[cfg(target_pointer_width = "64")]
        assert_eq!(
            18_446_744_073_709_551_615_u64.pack(),
            18_446_744_073_709_551_615
        );

        unsafe {
            assert_eq!(0u8, Packable::unpack(0));
            assert_eq!(255u8, Packable::unpack(255));
            assert_eq!(0u16, Packable::unpack(0));
            assert_eq!(65535u16, Packable::unpack(65535));
            assert_eq!(0u32, Packable::unpack(0));
            assert_eq!(4_294_967_295_u32, Packable::unpack(4_294_967_295));
            #[cfg(target_pointer_width = "64")]
            assert_eq!(0u64, Packable::unpack(0));
            #[cfg(target_pointer_width = "64")]
            assert_eq!(
                18_446_744_073_709_551_615_u64,
                Packable::unpack(18_446_744_073_709_551_615)
            );
        }
    }

    #[test]
    fn zst() {
        assert_eq!(<() as Packable>::MAX_BITS, 0);
        assert_eq!(().pack(), 0);
    }

    #[test]
    fn boolean() {
        assert_eq!(<bool as Packable>::MAX_BITS, 1);
        assert_eq!(false.pack(), 0);
        assert_eq!(true.pack(), 1);
        unsafe {
            assert!(!<bool as Packable>::unpack(0));
            assert!(<bool as Packable>::unpack(1));
        }
    }

    #[test]
    fn tuple() {
        assert_eq!(<(bool, u8) as Packable>::MAX_BITS, 9);

        assert_eq!((false, 0u8).pack(), 0x000);
        assert_eq!((false, 255u8).pack(), 0x0ff);
        assert_eq!((true, 0u8).pack(), 0x100);
        assert_eq!((true, 255u8).pack(), 0x1ff);
        assert_eq!((true, false).pack(), 0b10);

        unsafe {
            assert_eq!((false, 0u8), Packable::unpack(0x000));
            assert_eq!((false, 255u8), Packable::unpack(0x0ff));
            assert_eq!((true, 0u8), Packable::unpack(0x100));
            assert_eq!((true, 255u8), Packable::unpack(0x1ff));
            assert_eq!((true, false), Packable::unpack(0b10));
        }
    }

    #[test]
    fn array() {
        assert_eq!(<[u8; 3] as Packable>::MAX_BITS, 24);
        assert_eq!(<[u8; 4] as Packable>::MAX_BITS, 32);
        assert_eq!(<[bool; 4] as Packable>::MAX_BITS, 4);

        assert_eq!([0u8, 0, 0].pack(), 0x0000_0000);
        assert_eq!([0u8, 0, 255].pack(), 0x0000_00ff);
        assert_eq!([0u8, 255, 0].pack(), 0x0000_ff00);
        assert_eq!([0u8, 255, 255].pack(), 0x0000_ffff);
        assert_eq!([255u8, 0, 0].pack(), 0x00ff_0000);
        assert_eq!([255u8, 0, 255].pack(), 0x00ff_00ff);
        assert_eq!([255u8, 255, 0].pack(), 0x00ff_ff00);
        assert_eq!([255u8, 255, 255].pack(), 0x00ff_ffff);
        assert_eq!([true, false].pack(), 0b10);

        unsafe {
            assert_eq!([0u8, 0, 0], <[u8; 3] as Packable>::unpack(0x0000_0000));
            assert_eq!([0u8, 0, 255], <[u8; 3] as Packable>::unpack(0x0000_00ff));
            assert_eq!([0u8, 255, 0], <[u8; 3] as Packable>::unpack(0x0000_ff00));
            assert_eq!([0u8, 255, 255], <[u8; 3] as Packable>::unpack(0x0000_ffff));
            assert_eq!([255u8, 0, 0], <[u8; 3] as Packable>::unpack(0x00ff_0000));
            assert_eq!([255u8, 0, 255], <[u8; 3] as Packable>::unpack(0x00ff_00ff));
            assert_eq!([255u8, 255, 0], <[u8; 3] as Packable>::unpack(0x00ff_ff00));
            assert_eq!(
                [255u8, 255, 255],
                <[u8; 3] as Packable>::unpack(0x00ff_ffff)
            );
            assert_eq!([true, false], <[bool; 2] as Packable>::unpack(0b10));
        }
    }

    #[test]
    fn option() {
        assert_eq!(<Option<u8> as Packable>::MAX_BITS, 9);
        assert_eq!(<Option<bool> as Packable>::MAX_BITS, 2);

        assert_eq!(None::<u8>.pack(), 0x00);
        assert_eq!(Some(0u8).pack(), 0x01);
        assert_eq!(Some(255u8).pack(), 0x1FF);

        unsafe {
            assert_eq!(None::<u8>, Packable::unpack(0x00));
            assert_eq!(Some(0u8), Packable::unpack(0x01));
            assert_eq!(Some(255u8), Packable::unpack(0x1FF));
        }
    }

    #[test]
    fn result() {
        assert_eq!(<Result<u8, u8> as Packable>::MAX_BITS, 9);
        assert_eq!(<Result<bool, bool> as Packable>::MAX_BITS, 2);

        assert_eq!(Err::<u8, u8>(0u8).pack(), 0x00);
        assert_eq!(Ok::<u8, u8>(0u8).pack(), 0x01);
        assert_eq!(Err::<u8, u8>(255u8).pack(), 0x1FE);
        assert_eq!(Ok::<u8, u8>(255u8).pack(), 0x1FF);

        unsafe {
            assert_eq!(Err::<u8, u8>(0u8), Packable::unpack(0x00));
            assert_eq!(Ok::<u8, u8>(0u8), Packable::unpack(0x01));
            assert_eq!(Err::<u8, u8>(255u8), Packable::unpack(0x1FE));
            assert_eq!(Ok::<u8, u8>(255u8), Packable::unpack(0x1FF));
        }
    }
}
