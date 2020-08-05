// Copyright 2020 Parity Technologies
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Code derived from original work by Andrew Poelstra <apoelstra@wpsoftware.net>

// Rust Bitcoin Library
// Written in 2014 by
//	   Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! Big unsigned integer types.
//!
//! Implementation of a various large-but-fixed sized unsigned integer types.
//! The functions here are designed to be fast. There are optional `x86_64`
//! implementations for even more speed, hidden behind the `x64_arithmetic`
//! feature flag.


/// Conversion from decimal string error
#[derive(Debug, PartialEq)]
pub enum FromDecStrErr {
	/// Char not from range 0-9
	InvalidCharacter,
	/// Value does not fit into type
	InvalidLength,
}


impl std::fmt::Display for FromDecStrErr {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(
			f,
			"{}",
			match self {
				FromDecStrErr::InvalidCharacter => "a character is not in the range 0-9",
				FromDecStrErr::InvalidLength => "the number is too large for the type",
			}
		)
	}
}


impl std::error::Error for FromDecStrErr {}


#[macro_export]
macro_rules! construct_uint {
	( $(#[$attr:meta])* $visibility:vis struct $name:ident (1); ) => {
		$crate::construct_uint!{ @construct $(#[$attr])* $visibility struct $name (1); }

		impl std::convert::From<u128> for $name {
			fn from(value: u128) -> $name {
				$name([value as u64])
			}
		}

		impl $name {
			#[inline]
			pub const fn low_u128(&self) -> u128 {
				arr[0] as u128
			}

			#[inline]
			pub fn as_u128(&self) -> u128 {
				self.low_u128()
			}
		}

		impl std::convert::TryFrom<$name> for u128 {
			type Error = &'static str;

			#[inline]
			fn try_from(u: $name) -> std::result::Result<u128, &'static str> {
				let $name(arr) = u;
				Ok(arr[0] as u128)
			}
		}

		impl std::convert::TryFrom<$name> for i128 {
			type Error = &'static str;

			#[inline]
			fn try_from(u: $name) -> std::result::Result<i128, &'static str> {
				Ok(u128::from(u))
			}
		}
		
	};

	( $(#[$attr:meta])* $visibility:vis struct $name:ident ( $n_words:tt ); ) => {
			$crate::construct_uint! { @construct $(#[$attr])* $visibility struct $name ($n_words); }

			impl std::convert::From<u128> for $name {
				fn from(value: u128) -> $name {
					let mut ret = [0; $n_words];
					ret[0] = value as u64;
					ret[1] = (value >> 64) as u64;
					$name(ret)
				}
			}

			impl $name {
				/// Low 2 words (u128)
				#[inline]
				pub const fn low_u128(&self) -> u128 {
					let &$name(ref arr) = self;
					((arr[1] as u128) << 64) + arr[0] as u128
				}

				/// Conversion to u128 with overflow checking
				///
				/// # Panics
				///
				/// Panics if the number is larger than 2^128.
				#[inline]
				pub fn as_u128(&self) -> u128 {
					let &$name(ref arr) = self;
					for i in 2..$n_words {
						if arr[i] != 0 {
							panic!("Integer overflow when casting to u128")
						}

					}
					self.low_u128()
				}
			}

			impl std::convert::TryFrom<$name> for u128 {
				type Error = &'static str;

				#[inline]
				fn try_from(u: $name) -> std::result::Result<u128, &'static str> {
					let $name(arr) = u;
					for i in 2..$n_words {
						if arr[i] != 0 {
							return Err("integer overflow when casting to u128");
						}
					}
					Ok(((arr[1] as u128) << 64) + arr[0] as u128)
				}
			}

			impl std::convert::TryFrom<$name> for i128 {
				type Error = &'static str;

				#[inline]
				fn try_from(u: $name) -> std::result::Result<i128, &'static str> {
					let err_str = "integer overflow when casting to i128";
					let i = u128::try_from(u).map_err(|_| err_str)?;
					if i > i128::max_value() as u128 {
						Err(err_str)
					} else {
						Ok(i as i128)
					}
				}
			}
	};

	
	( @construct $(#[$attr:meta])* $visibility:vis struct $name:ident ( $n_words:tt ); ) => {
		/// Little-endian large integer type
		#[repr(C)]
		$(#[$attr])*
		#[derive(Copy, Clone)]
		$visibility struct $name (pub [u64; $n_words]);

		impl std::convert::From<i128> for $name {
			fn from(value: i128) -> $name {
				match value >= 0 {
					true => From::from(value as u128),
					false => { panic!("Unsigned integer can't be created from negative value"); }
				}
			}
		}

		/// Get a reference to the underlying little-endian words.
		impl AsRef<[u64]> for $name {
			#[inline]
			fn as_ref(&self) -> &[u64] {
				&self.0
			}
		}

		/// Get a mutable reference to the underlying little-endian words.
		impl AsMut<[u64]> for $name {
			#[inline]
			fn as_mut(&mut self) -> &mut [u64] {
				&mut self.0
			}
		}

		impl<'a> From<&'a $name> for $name {
			fn from(x: &'a $name) -> $name {
				*x
			}
		}

		impl $name {
			const WORD_BITS: usize = 64;
			/// Maximum value.
			pub const MAX: $name = $name([u64::max_value(); $n_words]);

			/// Conversion to u32
			#[inline]
			pub const fn low_u32(&self) -> u32 {
				let &$name(ref arr) = self;
				arr[0] as u32
			}

			/// Low word (u64)
			#[inline]
			pub const fn low_u64(&self) -> u64 {
				let &$name(ref arr) = self;
				arr[0]
			}

			/// Conversion to u32 with overflow checking
			///
			/// # Panics
			///
			/// Panics if the number is larger than 2^32.
			#[inline]
			pub fn as_u32(&self) -> u32 {
				let &$name(ref arr) = self;
				if !self.fits_word() ||  arr[0] > u32::max_value() as u64 {
					panic!("Integer overflow when casting to u32")
				}
				self.as_u64() as u32
			}

			/// Conversion to u64 with overflow checking
			///
			/// # Panics
			///
			/// Panics if the number is larger than u64::max_value().
			#[inline]
			pub fn as_u64(&self) -> u64 {
				let &$name(ref arr) = self;
				if !self.fits_word() {
					panic!("Integer overflow when casting to u64")
				}
				arr[0]
			}

			/// Conversion to usize with overflow checking
			///
			/// # Panics
			///
			/// Panics if the number is larger than usize::max_value().
			#[inline]
			pub fn as_usize(&self) -> usize {
				let &$name(ref arr) = self;
				if !self.fits_word() || arr[0] > usize::max_value() as u64 {
					panic!("Integer overflow when casting to usize")
				}
				arr[0] as usize
			}

			/// Whether this is zero.
			#[inline]
			pub fn is_zero(&self) -> bool {
				let &$name(ref arr) = self;
				for i in 0..$n_words { if arr[i] != 0 { return false; } }
				return true;
			}

			// Whether this fits u64.
			#[inline]
			fn fits_word(&self) -> bool {
				let &$name(ref arr) = self;
				for i in 1..$n_words { if arr[i] != 0 { return false; } }
				return true;
			}


			/// Return the least number of bits needed to represent the number
			#[inline]
			pub fn bits(&self) -> usize {
				let &$name(ref arr) = self;
				for i in 1..$n_words {
					if arr[$n_words - i] > 0 { return (0x40 * ($n_words - i + 1)) - arr[$n_words - i].leading_zeros() as usize; }
				}
				0x40 - arr[0].leading_zeros() as usize
			}

			/// Return if specific bit is set.
			///
			/// # Panics
			///
			/// Panics if `index` exceeds the bit width of the number.
			#[inline]
			pub const fn bit(&self, index: usize) -> bool {
				let &$name(ref arr) = self;
				arr[index / 64] & (1 << (index % 64)) != 0
			}

			/// Returns the number of leading zeros in the binary representation of self.
			pub fn leading_zeros(&self) -> u32 {
				let mut r = 0;
				for i in 0..$n_words {
					let w = self.0[$n_words - i - 1];
					if w == 0 {
						r += 64;
					} else {
						r += w.leading_zeros();
						break;
					}
				}
				r
			}

			/// Returns the number of leading zeros in the binary representation of self.
			pub fn trailing_zeros(&self) -> u32 {
				let mut r = 0;
				for i in 0..$n_words {
					let w = self.0[i];
					if w == 0 {
						r += 64;
					} else {
						r += w.trailing_zeros();
						break;
					}
				}
				r
			}

			/// Return specific byte.
			///
			/// # Panics
			///
			/// Panics if `index` exceeds the byte width of the number.
			#[inline]
			pub const fn byte(&self, index: usize) -> u8 {
				let &$name(ref arr) = self;
				(arr[index / 8] >> (((index % 8)) * 8)) as u8
			}

			
			/// Write to the slice in big-endian format.
			#[inline]
			pub fn put_big_endian(&self, bytes: &mut [u8]) {
				use $crate::byteorder::{ByteOrder, BigEndian};
				debug_assert!($n_words * 8 == bytes.len());
				for i in 0..$n_words {
					BigEndian::write_u64(&mut bytes[8 * i..], self.0[$n_words - i - 1]);
				}
			}

			/// Write to the slice in little-endian format.
			#[inline]
			pub fn put_little_endian(&self, bytes: &mut [u8]) {
				use $crate::byteorder::{ByteOrder, LittleEndian};
				debug_assert!($n_words * 8 == bytes.len());
				for i in 0..$n_words {
					LittleEndian::write_u64(&mut bytes[8 * i..], self.0[i]);
				}
			}

			#[inline]
			pub fn to_be_bytes(&self) -> [u8; $n_words*8] {
				let mut bytes = [0; $n_words*8];
				self.put_big_endian(&mut bytes);
				bytes
			}

			#[inline]
			pub fn to_le_bytes(&self) -> [u8; $n_words*8] {
				let mut bytes = [0; $n_words*8];
				self.put_little_endian(&mut bytes);
				bytes
			}


			/// Create `10**n` as this type.
			///
			/// # Panics
			///
			/// Panics if the result overflows the type.
			#[inline]
			pub fn exp10(n: usize) -> Self {
				match n {
					0 => Self::from(1u64),
					_ => Self::exp10(n - 1) * 10u32
				}
			}

			/// Zero (additive identity) of this type.
			#[inline]
			pub const fn zero() -> Self {
				Self([0; $n_words])
			}

			/// One (multiplicative identity) of this type.
			#[inline]
			pub fn one() -> Self {
				From::from(1u64)
			}

			/// The maximum value which can be inhabited by this type.
			#[inline]
			pub fn max_value() -> Self {
				let mut result = [0; $n_words];
				for i in 0..$n_words {
					result[i] = u64::max_value();
				}
				$name(result)
			}

			fn full_shl(self, shift: u32) -> [u64; $n_words + 1] {
				debug_assert!(shift < Self::WORD_BITS as u32);
				let mut u = [064; $n_words + 1];
				let u_lo = self.0[0] << shift;
				let u_hi = self.wrapping_shr(Self::WORD_BITS as u32 - shift);
				u[0] = u_lo;
				u[1..].copy_from_slice(&u_hi.0[..]);
				u
			}

			fn full_shr(u: [u64; $n_words + 1], shift: u32) -> Self {
				debug_assert!(shift < Self::WORD_BITS as u32);
				let mut res = Self::zero();
				for i in 0..$n_words {
					res.0[i] = u[i] >> shift;
				}
				// carry
				if shift > 0 {
					for i in 1..=$n_words {
						res.0[i - 1] |= u[i] << (Self::WORD_BITS as u32 - shift);
					}
				}
				res
			}

			fn full_mul_u64(self, by: u64) -> [u64; $n_words + 1] {
				let (prod, carry) = self.overflowing_mul_u64(by);
				let mut res = [0u64; $n_words + 1];
				res[..$n_words].copy_from_slice(&prod.0[..]);
				res[$n_words] = carry;
				res
			}

			fn div_mod_small(mut self, other: u64) -> (Self, Self) {
				let mut rem = 0u64;
				self.0.iter_mut().rev().for_each(|d| {
					let (q, r) = Self::div_mod_word(rem, *d, other);
					*d = q;
					rem = r;
				});
				(self, rem.into())
			}

			// See Knuth, TAOCP, Volume 2, section 4.3.1, Algorithm D.
			fn div_mod_knuth(self, mut v: Self, n: usize, m: usize) -> (Self, Self) {
				debug_assert!(self.bits() >= v.bits() && !v.fits_word());
				debug_assert!(n + m <= $n_words);
				// D1.
				// Make sure 64th bit in v's highest word is set.
				// If we shift both self and v, it won't affect the quotient
				// and the remainder will only need to be shifted back.
				let shift = v.0[n - 1].leading_zeros();
				v = v.wrapping_shl(shift);
				// u will store the remainder (shifted)
				let mut u = self.full_shl(shift);

				// quotient
				let mut q = Self::zero();
				let v_n_1 = v.0[n - 1];
				let v_n_2 = v.0[n - 2];

				// D2. D7.
				// iterate from m downto 0
				for j in (0..=m).rev() {
					let u_jn = u[j + n];

					// D3.
					// q_hat is our guess for the j-th quotient digit
					// q_hat = min(b - 1, (u_{j+n} * b + u_{j+n-1}) / v_{n-1})
					// b = 1 << WORD_BITS
					// Theorem B: q_hat >= q_j >= q_hat - 2
					let mut q_hat = if u_jn < v_n_1 {
						let (mut q_hat, mut r_hat) = Self::div_mod_word(u_jn, u[j + n - 1], v_n_1);
						// this loop takes at most 2 iterations
						loop {
							// check if q_hat * v_{n-2} > b * r_hat + u_{j+n-2}
							let (hi, lo) = Self::split_u128(u128::from(q_hat) * u128::from(v_n_2));
							if (hi, lo) <= (r_hat, u[j + n - 2]) {
								break;
							}
							// then iterate till it doesn't hold
							q_hat -= 1;
							let (new_r_hat, overflow) = r_hat.overflowing_add(v_n_1);
							r_hat = new_r_hat;
							// if r_hat overflowed, we're done
							if overflow {
								break;
							}
						}
						q_hat
					} else {
						// here q_hat >= q_j >= q_hat - 1
						u64::max_value()
					};

					// ex. 20:
					// since q_hat * v_{n-2} <= b * r_hat + u_{j+n-2},
					// either q_hat == q_j, or q_hat == q_j + 1

					// D4.
					// let's assume optimistically q_hat == q_j
					// subtract (q_hat * v) from u[j..]
					let q_hat_v = v.full_mul_u64(q_hat);
					// u[j..] -= q_hat_v;
					let c = Self::sub_slice(&mut u[j..], &q_hat_v[..n + 1]);

					// D6.
					// actually, q_hat == q_j + 1 and u[j..] has overflowed
					// highly unlikely ~ (1 / 2^63)
					if c {
						q_hat -= 1;
						// add v to u[j..]
						let c = Self::add_slice(&mut u[j..], &v.0[..n]);
						u[j + n] = u[j + n].wrapping_add(u64::from(c));
					}

					// D5.
					q.0[j] = q_hat;
				}

				// D8.
				let remainder = Self::full_shr(u, shift);

				(q, remainder)
			}

			// Returns the least number of words needed to represent the nonzero number
			fn words(bits: usize) -> usize {
				debug_assert!(bits > 0);
				1 + (bits - 1) / Self::WORD_BITS
			}

			/// Returns a pair `(self / other, self % other)`.
			///
			/// # Panics
			///
			/// Panics if `other` is zero.
			pub fn div_mod(mut self, mut other: Self) -> (Self, Self) {
				use std::cmp::Ordering;

				let my_bits = self.bits();
				let your_bits = other.bits();

				assert!(your_bits != 0, "division by zero");

				// Early return in case we are dividing by a larger number than us
				if my_bits < your_bits {
					return (Self::zero(), self);
				}

				if your_bits <= Self::WORD_BITS {
					return self.div_mod_small(other.low_u64());
				}

				let (n, m) = {
					let my_words = Self::words(my_bits);
					let your_words = Self::words(your_bits);
					(your_words, my_words - your_words)
				};

				self.div_mod_knuth(other, n, m)
			}

			/// Fast exponentiation by squaring
			/// https://en.wikipedia.org/wiki/Exponentiation_by_squaring
			///
			/// # Panics
			///
			/// Panics if the result overflows the type.
			pub fn pow(self, expon: Self) -> Self {
				if expon.is_zero() {
					return Self::one()
				}
				let is_even = |x : &Self| x.low_u64() & 1 == 0;

				let u_one = Self::one();
				let mut y = u_one;
				let mut n = expon;
				let mut x = self;
				while n > u_one {
					if is_even(&n) {
						x = x * x;
						n = n.wrapping_shr(1);
					} else {
						y = x * y;
						x = x * x;
						// to reduce odd number by 1 we should just clear the last bit
						n.0[$n_words-1] = n.0[$n_words-1] & ((!0u64)>>1);
						n = n.wrapping_shr(1);
					}
				}
				x * y
			}

			/// Fast exponentiation by squaring. Returns result and overflow flag.
			pub fn overflowing_pow(self, expon: Self) -> (Self, bool) {
				if expon.is_zero() { return (Self::one(), false) }

				let is_even = |x : &Self| x.low_u64() & 1 == 0;

				let u_one = Self::one();
				let mut y = u_one;
				let mut n = expon;
				let mut x = self;
				let mut overflow = false;

				while n > u_one {
					if is_even(&n) {
						x = $crate::overflowing!(x.overflowing_mul(x), overflow);
						n = n.wrapping_shr(1);
					} else {
						y = $crate::overflowing!(x.overflowing_mul(y), overflow);
						x = $crate::overflowing!(x.overflowing_mul(x), overflow);
						n = (n - u_one).wrapping_shr(1);
					}
				}
				let res = $crate::overflowing!(x.overflowing_mul(y), overflow);
				(res, overflow)
			}

			/// Checked exponentiation. Returns `None` if overflow occurred.
			pub fn checked_pow(self, expon: $name) -> Option<$name> {
				match self.overflowing_pow(expon) {
					(_, true) => None,
					(val, _) => Some(val),
				}
			}

			/// Add with overflow.
			#[inline(always)]
			pub fn overflowing_add(self, other: $name) -> ($name, bool) {
				$crate::uint_overflowing_binop!(
					$name,
					$n_words,
					self,
					other,
					u64::overflowing_add
				)
			}

			/// Addition which saturates at the maximum value (Self::max_value()).
			pub fn saturating_add(self, other: $name) -> $name {
				match self.overflowing_add(other) {
					(_, true) => $name::max_value(),
					(val, false) => val,
				}
			}

			/// Checked addition. Returns `None` if overflow occurred.
			pub fn checked_add(self, other: $name) -> Option<$name> {
				match self.overflowing_add(other) {
					(_, true) => None,
					(val, _) => Some(val),
				}
			}

			/// Subtraction which underflows and returns a flag if it does.
			#[inline(always)]
			pub fn overflowing_sub(self, other: $name) -> ($name, bool) {
				$crate::uint_overflowing_binop!(
					$name,
					$n_words,
					self,
					other,
					u64::overflowing_sub
				)
			}

			/// Subtraction which saturates at zero.
			pub fn saturating_sub(self, other: $name) -> $name {
				match self.overflowing_sub(other) {
					(_, true) => $name::zero(),
					(val, false) => val,
				}
			}

			/// Checked subtraction. Returns `None` if overflow occurred.
			pub fn checked_sub(self, other: $name) -> Option<$name> {
				match self.overflowing_sub(other) {
					(_, true) => None,
					(val, _) => Some(val),
				}
			}

			/// Multiply with overflow, returning a flag if it does.
			#[inline(always)]
			pub fn overflowing_mul(self, other: $name) -> ($name, bool) {
				$crate::uint_overflowing_mul!($name, $n_words, self, other)
			}

			/// Multiplication which saturates at the maximum value..
			pub fn saturating_mul(self, other: $name) -> $name {
				match self.overflowing_mul(other) {
					(_, true) => $name::max_value(),
					(val, false) => val,
				}
			}

			/// Checked multiplication. Returns `None` if overflow occurred.
			pub fn checked_mul(self, other: $name) -> Option<$name> {
				match self.overflowing_mul(other) {
					(_, true) => None,
					(val, _) => Some(val),
				}
			}

			
			/// Checked division. Returns `None` if `other == 0`.
			pub fn checked_div(self, other: $name) -> Option<$name> {
				if other.is_zero() {
					None
				} else {
					Some(self.div_mod(other).0)
				}
			}

			/// Checked modulus. Returns `None` if `other == 0`.
			pub fn checked_rem(self, other: $name) -> Option<$name> {
				if other.is_zero() {
					None
				} else {
					Some(self.div_mod(other).1)
				}
			}

			/// Negation with overflow.
			pub fn overflowing_neg(self) -> ($name, bool) {
				if self.is_zero() {
					(self, false)
				} else {
					(!self, true)
				}
			}

			/// Checked negation. Returns `None` unless `self == 0`.
			pub fn checked_neg(self) -> Option<$name> {
				match self.overflowing_neg() {
					(_, true) => None,
					(zero, false) => Some(zero),
				}
			}

			fn wrapping_shr(self, rhs: u32) -> $name {
				let shift = rhs as usize;
				let $name(ref original) = self;
				let mut ret = [0u64; $n_words];
				let word_shift = shift / 64;
				let bit_shift = shift % 64;

				// shift
				for i in word_shift..$n_words {
					ret[i - word_shift] = original[i] >> bit_shift;
				}

				// Carry
				if bit_shift > 0 {
					for i in word_shift+1..$n_words {
						ret[i - word_shift - 1] += original[i] << (64 - bit_shift);
					}
				}

				$name(ret)
			}

			pub fn overflowing_shr(self, rhs: u32) -> ($name, bool) {
                (self.wrapping_shr(rhs), (rhs > ($n_words*64 - 1)))
			}
			
			pub fn checked_shr(self, rhs: u32) -> Option<$name> {
				match self.overflowing_shr(rhs) {
					(_, true) => None,
					(val, false) => Some(val),
				}
			}

			fn wrapping_shl(self, lhs: u32) -> $name {
				let shift = lhs as usize;
				let $name(ref original) = self;
				let mut ret = [0u64; $n_words];
				let word_shift = shift / 64;
				let bit_shift = shift % 64;

				// shift
				for i in word_shift..$n_words {
					ret[i] = original[i - word_shift] << bit_shift;
				}
				// carry
				if bit_shift > 0 {
					for i in word_shift+1..$n_words {
						ret[i] += original[i - 1 - word_shift] >> (64 - bit_shift);
					}
				}
				$name(ret)
			}

			pub fn overflowing_shl(self, lhs: u32) -> ($name, bool) {
                (self.wrapping_shl(lhs), (lhs > ($n_words*64 - 1)))
			}
			
			pub fn checked_shl(self, lhs: u32) -> Option<$name> {
				match self.overflowing_shl(lhs) {
					(_, true) => None,
					(val, false) => Some(val),
				}
			}
		

			#[inline(always)]
			fn div_mod_word(hi: u64, lo: u64, y: u64) -> (u64, u64) {
				debug_assert!(hi < y);
				// NOTE: this is slow (__udivti3)
				// let x = (u128::from(hi) << 64) + u128::from(lo);
				// let d = u128::from(d);
				// ((x / d) as u64, (x % d) as u64)
				// TODO: look at https://gmplib.org/~tege/division-paper.pdf
				const TWO32: u64 = 1 << 32;
				let s = y.leading_zeros();
				let y = y << s;
				let (yn1, yn0) = Self::split(y);
				let un32 = (hi << s) | lo.checked_shr(64 - s).unwrap_or(0);
				let un10 = lo << s;
				let (un1, un0) = Self::split(un10);
				let mut q1 = un32 / yn1;
				let mut rhat = un32 - q1 * yn1;

				while q1 >= TWO32 || q1 * yn0 > TWO32 * rhat + un1 {
					q1 -= 1;
					rhat += yn1;
					if rhat >= TWO32 {
						break;
					}
				}

				let un21 = un32.wrapping_mul(TWO32).wrapping_add(un1).wrapping_sub(q1.wrapping_mul(y));
				let mut q0 = un21 / yn1;
				rhat = un21.wrapping_sub(q0.wrapping_mul(yn1));

				while q0 >= TWO32 || q0 * yn0 > TWO32 * rhat + un0 {
					q0 -= 1;
					rhat += yn1;
					if rhat >= TWO32 {
						break;
					}
				}

				let rem = un21.wrapping_mul(TWO32).wrapping_add(un0).wrapping_sub(y.wrapping_mul(q0));
				(q1 * TWO32 + q0, rem >> s)
			}

			#[inline(always)]
			fn add_slice(a: &mut [u64], b: &[u64]) -> bool {
				Self::binop_slice(a, b, u64::overflowing_add)
			}

			#[inline(always)]
			fn sub_slice(a: &mut [u64], b: &[u64]) -> bool {
				Self::binop_slice(a, b, u64::overflowing_sub)
			}

			#[inline(always)]
			fn binop_slice(a: &mut [u64], b: &[u64], binop: impl Fn(u64, u64) -> (u64, bool) + Copy) -> bool {
				let mut c = false;
				a.iter_mut().zip(b.iter()).for_each(|(x, y)| {
					let (res, carry) = Self::binop_carry(*x, *y, c, binop);
					*x = res;
					c = carry;
				});
				c
			}

			#[inline(always)]
			fn binop_carry(a: u64, b: u64, c: bool, binop: impl Fn(u64, u64) -> (u64, bool)) -> (u64, bool) {
				let (res1, overflow1) = b.overflowing_add(u64::from(c));
				let (res2, overflow2) = binop(a, res1);
				(res2, overflow1 || overflow2)
			}

			#[inline(always)]
			const fn mul_u64(a: u64, b: u64, carry: u64) -> (u64, u64) {
				let (hi, lo) = Self::split_u128(a as u128 * b as u128 + carry as u128);
				(lo, hi)
			}

			#[inline(always)]
			const fn split(a: u64) -> (u64, u64) {
				(a >> 32, a & 0xFFFF_FFFF)
			}

			#[inline(always)]
			const fn split_u128(a: u128) -> (u64, u64) {
				((a >> 64) as _, (a & 0xFFFFFFFFFFFFFFFF) as _)
			}


			/// Overflowing multiplication by u64.
			/// Returns the result and carry.
			fn overflowing_mul_u64(mut self, other: u64) -> (Self, u64) {
				let mut carry = 0u64;

				for d in self.0.iter_mut() {
					let (res, c) = Self::mul_u64(*d, other, carry);
					*d = res;
					carry = c;
				}

				(self, carry)
			}

			/// Converts from big endian representation bytes in memory.
			pub fn from_big_endian(slice: &[u8]) -> Self {
				use $crate::byteorder::{ByteOrder, BigEndian};
				assert!($n_words * 8 >= slice.len());

				let mut padded = [0u8; $n_words * 8];
				padded[$n_words * 8 - slice.len() .. $n_words * 8].copy_from_slice(&slice);

				let mut ret = [0; $n_words];
				for i in 0..$n_words {
					ret[$n_words - i - 1] = BigEndian::read_u64(&padded[8 * i..]);
				}

				$name(ret)
			}

			/// Converts from little endian representation bytes in memory.
			pub fn from_little_endian(slice: &[u8]) -> Self {
				use $crate::byteorder::{ByteOrder, LittleEndian};
				assert!($n_words * 8 >= slice.len());

				let mut padded = [0u8; $n_words * 8];
				padded[0..slice.len()].copy_from_slice(&slice);

				let mut ret = [0; $n_words];
				for i in 0..$n_words {
					ret[i] = LittleEndian::read_u64(&padded[8 * i..]);
				}

				$name(ret)
			}
		}

		impl std::default::Default for $name {
			fn default() -> Self {
				$name::zero()
			}
		}

		impl std::convert::From<u64> for $name {
			fn from(value: u64) -> $name {
				let mut ret = [0; $n_words];
				ret[0] = value;
				$name(ret)
			}
		}

		$crate::impl_map_from!($name, u8, u64);
		$crate::impl_map_from!($name, u16, u64);
		$crate::impl_map_from!($name, u32, u64);
		$crate::impl_map_from!($name, usize, u64);

		impl std::convert::From<i64> for $name {
			fn from(value: i64) -> $name {
				match value >= 0 {
					true => From::from(value as u64),
					false => { panic!("Unsigned integer can't be created from negative value"); }
				}
			}
		}

		$crate::impl_map_from!($name, i8, i64);
		$crate::impl_map_from!($name, i16, i64);
		$crate::impl_map_from!($name, i32, i64);
		$crate::impl_map_from!($name, isize, i64);
		$crate::impl_try_from_for_primitive!($name, u8);
		$crate::impl_try_from_for_primitive!($name, u16);
		$crate::impl_try_from_for_primitive!($name, u32);
		$crate::impl_try_from_for_primitive!($name, usize);
		$crate::impl_try_from_for_primitive!($name, u64);
		$crate::impl_try_from_for_primitive!($name, i8);
		$crate::impl_try_from_for_primitive!($name, i16);
		$crate::impl_try_from_for_primitive!($name, i32);
		$crate::impl_try_from_for_primitive!($name, isize);
		$crate::impl_try_from_for_primitive!($name, i64);

		$crate::impl_checked_assignop_from!(AddAssign, add_assign, checked_add, $name);
		$crate::impl_checked_binop_from!(Add, add, checked_add, $name);

		$crate::impl_checked_assignop_from!(SubAssign, sub_assign, checked_sub, $name);
		$crate::impl_checked_binop_from!(Sub, sub, checked_sub, $name);

		$crate::impl_checked_assignop_from!(DivAssign, div_assign, checked_div, $name);
		$crate::impl_checked_binop_from!(Div, div, checked_div, $name);

		$crate::impl_checked_assignop_from!(RemAssign, rem_assign, checked_rem, $name);
		$crate::impl_checked_binop_from!(Rem, rem, checked_rem, $name);

		//all other impls
		$crate::impl_mul_from!($name, $name);
		


		$crate::impl_mul_for_primitive!($name, u8);
		$crate::impl_mul_for_primitive!($name, u16);
		$crate::impl_mul_for_primitive!($name, u32);
		$crate::impl_mul_for_primitive!($name, u64);
		$crate::impl_mul_for_primitive!($name, usize);
		$crate::impl_mul_for_primitive!($name, i8);
		$crate::impl_mul_for_primitive!($name, i16);
		$crate::impl_mul_for_primitive!($name, i32);
		$crate::impl_mul_for_primitive!($name, i64);
		$crate::impl_mul_for_primitive!($name, isize);


		impl std::ops::BitAnd<$name> for $name {
			type Output = $name;

			#[inline]
			fn bitand(self, other: $name) -> $name {
				let $name(ref arr1) = self;
				let $name(ref arr2) = other;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = arr1[i] & arr2[i];
				}
				$name(ret)
			}
		}

		impl std::ops::BitXor<$name> for $name {
			type Output = $name;

			#[inline]
			fn bitxor(self, other: $name) -> $name {
				let $name(ref arr1) = self;
				let $name(ref arr2) = other;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = arr1[i] ^ arr2[i];
				}
				$name(ret)
			}
		}

		impl std::ops::BitOr<$name> for $name {
			type Output = $name;

			#[inline]
			fn bitor(self, other: $name) -> $name {
				let $name(ref arr1) = self;
				let $name(ref arr2) = other;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = arr1[i] | arr2[i];
				}
				$name(ret)
			}
		}

		impl std::ops::Not for $name {
			type Output = $name;

			#[inline]
			fn not(self) -> $name {
				let $name(ref arr) = self;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = !arr[i];
				}
				$name(ret)
			}
		}

		impl<T> std::ops::Shl<T> for $name where T: TryInto<u32>  {
			type Output = $name;

			fn shl(self, shift: T) -> $name {
				if let Ok(shift) = shift.try_into() {
					let (result, overflow) = self.overflowing_shl(shift);
					$crate::panic_on_overflow_checked!(overflow);
					result
				} else {
					panic!("TryInto convert error")
				}
			}
		}

		impl<'a, T> std::ops::Shl<T> for &'a $name where T: TryInto<u32> {
			type Output = $name;
			fn shl(self, shift: T) -> $name {
				*self << shift
			}
		}

		impl<T> std::ops::ShlAssign<T> for $name where T: TryInto<u32> {
			fn shl_assign(&mut self, shift: T) {
				*self = *self << shift;
			}
		}

		impl<T> std::ops::Shr<T> for $name where T: TryInto<u32>{
			type Output = $name;

			fn shr(self, shift: T) -> $name {
				if let Ok(shift) = shift.try_into() {
					let (result, overflow) = self.overflowing_shr(shift);
					$crate::panic_on_overflow_checked!(overflow);
					result
				} else {
					panic!("TryInto convert error")
				}
			}
		}

		impl<'a, T> std::ops::Shr<T> for &'a $name where T: TryInto<u32> {
			type Output = $name;
			fn shr(self, shift: T) -> $name {
				*self >> shift
			}
		}

		impl<T> std::ops::ShrAssign<T> for $name where T: TryInto<u32> {
			fn shr_assign(&mut self, shift: T) {
				*self = *self >> shift;
			}
		}

		// We implement `Eq` and `Hash` manually to workaround
		// https://github.com/rust-lang/rust/issues/61415
		impl std::cmp::PartialEq for $name {
			fn eq(&self, other: &$name) -> bool {
				self.as_ref() == other.as_ref()
			}
		}

		impl std::cmp::Eq for $name {}

		impl std::hash::Hash for $name {
			fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
				// use the impl as slice &[u64]
				self.as_ref().hash(state);
			}
		}

		impl std::cmp::Ord for $name {
			fn cmp(&self, other: &$name) -> std::cmp::Ordering {
                self.as_ref().iter().rev().cmp(other.as_ref().iter().rev())
			}
		}

		impl std::cmp::PartialOrd for $name {
			fn partial_cmp(&self, other: &$name) -> Option<std::cmp::Ordering> {
				Some(self.cmp(other))
			}
		}

		impl std::fmt::Debug for $name {
			fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
				std::fmt::Display::fmt(self, f)
			}
		}


		impl std::fmt::Display for $name {
			fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
				if self.is_zero() {
					return std::write!(f, "0");
				}

				let mut buf = [0_u8; $n_words*20];
				let mut i = buf.len() - 1;
				let mut current = *self;
				let ten = $name::from(10);

				loop {
					let digit = (current % ten).low_u64() as u8;
					buf[i] = digit + b'0';
					current = current / ten;
					if current.is_zero() {
						break;
					}
					i -= 1;
				}

				// sequence of `'0'..'9'` chars is guaranteed to be a valid UTF8 string
				let s = unsafe {
					std::str::from_utf8_unchecked(&buf[i..])
				};
				f.write_str(s)
			}
		}

		impl std::fmt::LowerHex for $name {
			fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
				let &$name(ref data) = self;
				if f.alternate() {
					std::write!(f, "0x")?;
				}
				// special case.
				if self.is_zero() {
					return std::write!(f, "0");
				}

				let mut latch = false;
				for ch in data.iter().rev() {
					for x in 0..16 {
						let nibble = (ch & (15u64 << ((15 - x) * 4) as u64)) >> (((15 - x) * 4) as u64);
						if !latch {
							latch = nibble != 0;
						}

						if latch {
							std::write!(f, "{:x}", nibble)?;
						}
					}
				}
				Ok(())
			}
		}
		
		impl $crate::rand::distributions::Distribution<$name> for $crate::rand::distributions::Standard {
			#[inline]
			fn sample<R: $crate::rand::Rng + ?Sized>(&self, rng: &mut R) -> $name {
				$name(rng.gen())
			}
		}

		impl std::str::FromStr for $name {
			type Err = $crate::FromDecStrErr;

			fn from_str(value: &str) -> std::result::Result<$name, Self::Err> {
				if !value.bytes().all(|b| b >= 48 && b <= 57) {
					return Err($crate::FromDecStrErr::InvalidCharacter)
				}

				let mut res = Self::default();
				for b in value.bytes().map(|b| b - 48) {
					let (r, overflow) = res.overflowing_mul_u64(10);
					if overflow > 0 {
						return Err($crate::FromDecStrErr::InvalidLength);
					}
					let (r, overflow) = r.overflowing_add(b.into());
					if overflow {
						return Err($crate::FromDecStrErr::InvalidLength);
					}
					res = r;
				}
				Ok(res)
			}
		}

		impl std::convert::From<&'static str> for $name {
			fn from(s: &'static str) -> Self {
				s.parse().unwrap()
			}
		}
	}
}
