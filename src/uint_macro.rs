#![allow(unused_macros)]


#[macro_export]
#[doc(hidden)]
macro_rules! impl_map_from {
	($thing:ident, $from:ty, $to:ty) => {
		impl From<$from> for $thing {
			fn from(value: $from) -> $thing {
				From::from(value as $to)
			}
		}
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! impl_try_from_for_primitive {
	($from:ident, $to:ty) => {
		impl std::convert::TryFrom<$from> for $to {
			type Error = &'static str;

			#[inline]
			fn try_from(u: $from) -> std::result::Result<$to, &'static str> {
				let $from(arr) = u;
				if !u.fits_word() || arr[0] > <$to>::max_value() as u64 {
					Err(concat!(
						"integer overflow when casting to ",
						stringify!($to)
					))
				} else {
					Ok(arr[0] as $to)
				}
			}
		}
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! uint_overflowing_binop {
	($name:ident, $n_words: tt, $self_expr: expr, $other: expr, $fn:expr) => {{
		let $name(ref me) = $self_expr;
		let $name(ref you) = $other;

		let mut ret = [0u64; $n_words];
		let ret_ptr = &mut ret as *mut [u64; $n_words] as *mut u64;
		let mut carry = 0u64;
		$crate::static_assertions::const_assert!(
			std::isize::MAX as usize / std::mem::size_of::<u64>() > $n_words
		);

		// `unroll!` is recursive, but doesn’t use `$crate::unroll`, so we need to ensure that it
		// is in scope unqualified.
		use $crate::unroll;
		unroll! {
			for i in 0..$n_words {
				use std::ptr;

				if carry != 0 {
					let (res1, overflow1) = ($fn)(me[i], you[i]);
					let (res2, overflow2) = ($fn)(res1, carry);

					unsafe {
						// SAFETY: `i` is within bounds and `i * size_of::<u64>() < isize::MAX`
						*ret_ptr.offset(i as _) = res2
					}
					carry = (overflow1 as u8 + overflow2 as u8) as u64;
				} else {
					let (res, overflow) = ($fn)(me[i], you[i]);

					unsafe {
						// SAFETY: `i` is within bounds and `i * size_of::<u64>() < isize::MAX`
						*ret_ptr.offset(i as _) = res
					}

					carry = overflow as u64;
				}
			}
		}

		($name(ret), carry > 0)
		}};
}

#[macro_export]
#[doc(hidden)]
macro_rules! uint_full_mul_reg {
	($name:ident, 8, $self_expr:expr, $other:expr) => {
		$crate::uint_full_mul_reg!($name, 8, $self_expr, $other, |a, b| a != 0 || b != 0);
	};
	($name:ident, $n_words:tt, $self_expr:expr, $other:expr) => {
		$crate::uint_full_mul_reg!($name, $n_words, $self_expr, $other, |_, _| true);
	};
	($name:ident, $n_words:tt, $self_expr:expr, $other:expr, $check:expr) => {{
		{
			#![allow(unused_assignments)]

			let $name(ref me) = $self_expr;
			let $name(ref you) = $other;
			let mut ret = [0u64; $n_words * 2];

			use $crate::unroll;
			unroll! {
				for i in 0..$n_words {
					let mut carry = 0u64;
					let b = you[i];

					unroll! {
						for j in 0..$n_words {
							if $check(me[j], carry) {
								let a = me[j];

								let (hi, low) = Self::split_u128(a as u128 * b as u128);

								let overflow = {
									let existing_low = &mut ret[i + j];
									let (low, o) = low.overflowing_add(*existing_low);
									*existing_low = low;
									o
								};

								carry = {
									let existing_hi = &mut ret[i + j + 1];
									let hi = hi + overflow as u64;
									let (hi, o0) = hi.overflowing_add(carry);
									let (hi, o1) = hi.overflowing_add(*existing_hi);
									*existing_hi = hi;

									(o0 | o1) as u64
								}
							}
						}
					}
				}
			}

			ret
		}
	}};
}

#[macro_export]
#[doc(hidden)]
macro_rules! uint_overflowing_mul {
	($name:ident, $n_words: tt, $self_expr: expr, $other: expr) => {{
		let ret: [u64; $n_words * 2] =
			$crate::uint_full_mul_reg!($name, $n_words, $self_expr, $other);

		// The safety of this is enforced by the compiler
		let ret: [[u64; $n_words]; 2] = unsafe { std::mem::transmute(ret) };

		// The compiler WILL NOT inline this if you remove this annotation.
		#[inline(always)]
		fn any_nonzero(arr: &[u64; $n_words]) -> bool {
			use $crate::unroll;
			unroll! {
				for i in 0..$n_words {
					if arr[i] != 0 {
						return true;
					}
				}
			}

			false
		}

		($name(ret[0]), any_nonzero(&ret[1]))
	}};
}

#[macro_export]
#[doc(hidden)]
macro_rules! overflowing {
	($op: expr, $overflow: expr) => {{
		let (overflow_x, overflow_overflow) = $op;
		$overflow |= overflow_overflow;
		overflow_x
	}};
	($op: expr) => {{
		let (overflow_x, _overflow_overflow) = $op;
		overflow_x
	}};
}

#[macro_export]
#[doc(hidden)]
macro_rules! panic_on_overflow_checked {
	($name: expr) => {
		if $name {
			panic!("arithmetic operation overflow")
		}
	};
}


#[macro_export]
#[doc(hidden)]
macro_rules! panic_on_overflow {
	() => {
		panic!("arithmetic operation overflow")
	};
}




macro_rules! forward_val_assign_ex {
    (impl<$($imp_l:lifetime, )*$($imp_i:ident : $imp_p:path),+> $imp:ident<$res2:ty> for $res:ty, $method:ident) => {
        impl<$($imp_l, )*$($imp_i : $imp_p),+> $imp<$res2> for $res {
            #[inline]
            fn $method(&mut self, other: $res2) {
                self.$method(&other);
            }
        }
    };
}


#[macro_export]
#[doc(hidden)]
macro_rules! impl_mul_from {
	($name: ty, $other: ident) => {
		impl std::ops::Mul<$other> for $name {
			type Output = $name;

			fn mul(self, other: $other) -> $name {
				let bignum: $name = other.into();
				let (result, overflow) = self.overflowing_mul(bignum);
				$crate::panic_on_overflow_checked!(overflow);
				result
			}
		}

		impl<'a> std::ops::Mul<&'a $other> for $name {
			type Output = $name;

			fn mul(self, other: &'a $other) -> $name {
				let bignum: $name = (*other).into();
				let (result, overflow) = self.overflowing_mul(bignum);
				$crate::panic_on_overflow_checked!(overflow);
				result
			}
		}

		impl<'a> std::ops::Mul<&'a $other> for &'a $name {
			type Output = $name;

			fn mul(self, other: &'a $other) -> $name {
				let bignum: $name = (*other).into();
				let (result, overflow) = self.overflowing_mul(bignum);
				$crate::panic_on_overflow_checked!(overflow);
				result
			}
		}

		impl<'a> std::ops::Mul<$other> for &'a $name {
			type Output = $name;

			fn mul(self, other: $other) -> $name {
				let bignum: $name = other.into();
				let (result, overflow) = self.overflowing_mul(bignum);
				$crate::panic_on_overflow_checked!(overflow);
				result
			}
		}

		impl std::ops::MulAssign<$other> for $name {
			fn mul_assign(&mut self, other: $other) {
				let result = *self * other;
				*self = result
			}
		}
	};
}




#[macro_export]
#[doc(hidden)]
macro_rules! impl_mul_for_primitive {
	($name: ty, $other: ident) => {
		impl std::ops::Mul<$other> for $name {
			type Output = $name;

			fn mul(self, other: $other) -> $name {
				let (result, carry) = self.overflowing_mul_u64(other as u64);
				$crate::panic_on_overflow_checked!(carry > 0);
				result
			}
		}

		impl<'a> std::ops::Mul<&'a $other> for $name {
			type Output = $name;

			fn mul(self, other: &'a $other) -> $name {
				let (result, carry) = self.overflowing_mul_u64(*other as u64);
				$crate::panic_on_overflow_checked!(carry > 0);
				result
			}
		}

		impl<'a> std::ops::Mul<&'a $other> for &'a $name {
			type Output = $name;

			fn mul(self, other: &'a $other) -> $name {
				let (result, carry) = self.overflowing_mul_u64(*other as u64);
				$crate::panic_on_overflow_checked!(carry > 0);
				result
			}
		}

		impl<'a> std::ops::Mul<$other> for &'a $name {
			type Output = $name;

			fn mul(self, other: $other) -> $name {
				let (result, carry) = self.overflowing_mul_u64(other as u64);
				$crate::panic_on_overflow_checked!(carry > 0);
				result
			}
		}

		impl std::ops::MulAssign<$other> for $name {
			fn mul_assign(&mut self, other: $other) {
				let result = *self * (other as u64);
				*self = result
			}
		}
	};
}



#[macro_export]
#[doc(hidden)]
macro_rules! impl_checked_assignop_from {
	($op: ident, $method:ident, $checked_op: ident, $name: ty) => {
		impl<T:Into<$name>> std::ops::$op<T> for $name {
            #[inline]
			fn $method(&mut self, other: T) {
                let bignum: $name = other.into();
				match self.$checked_op(bignum) {
                    Some(result) => *self=result,
                    None => $crate::panic_on_overflow!()
                };
			}
        }
	};
}


#[macro_export]
#[doc(hidden)]
macro_rules! impl_checked_binop_from{
	($op: ident, $method:ident, $checked_op: ident, $name: ty) => {
		impl<T:Into<$name>> std::ops::$op<T> for $name {
			type Output = $name;

            #[inline]
			fn $method(self, other: T) -> Self::Output {
				let bignum: $name = other.into();
				match self.$checked_op(bignum) {
                    Some(result) => result,
                    None => $crate::panic_on_overflow!()
                }
			}
        }
        
        
        impl<'a, T:Into<$name>> std::ops::$op<T> for &'a $name {
			type Output = $name;

            #[inline]
			fn $method(self, other: T) -> Self::Output {
				let bignum: $name = other.into();
				match (*self).$checked_op(bignum) {
                    Some(result) => result,
                    None => $crate::panic_on_overflow!()
                }
			}
        }
        
	};
}

