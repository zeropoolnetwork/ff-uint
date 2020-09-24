use crate::Uint;
use crate::{BitIteratorBE, BitIterBE};

pub trait PrimeFieldParams {
    type Inner:Uint;
    const MODULUS: Self::Inner;
    const MODULUS_BITS: u32;
    const REPR_SHAVE_BITS: u32;
    const R: Self::Inner;
    const R2: Self::Inner;
    const INV: u64;
    const GENERATOR: Self::Inner;
    const S: u32;
    const ROOT_OF_UNITY: Self::Inner;
}


#[derive(Debug, PartialEq)]
pub enum LegendreSymbol {
    Zero = 0,
    QuadraticResidue = 1,
    QuadraticNonResidue = -1,
}

pub trait Field : 
    Sized + 
    Clone + 
    Copy + 
    Default +
    std::cmp::PartialEq +
    std::cmp::Eq +
    std::ops::Add<Self, Output=Self> +
    std::ops::Sub<Self, Output=Self> +
    std::ops::Mul<Self, Output=Self> +
    std::ops::Mul<u64, Output=Self> +
    std::ops::Div<Self, Output=Self> +
    std::ops::Neg<Output=Self> +
    std::ops::AddAssign<Self> +
    std::ops::SubAssign<Self> +
    std::ops::MulAssign<Self> +
    std::ops::MulAssign<u64> +
    std::ops::DivAssign<Self> +
    std::fmt::Debug +
    std::fmt::Display +
{
    const ZERO: Self;
    const ONE: Self;
    
    fn random<R: rand::Rng + ?Sized>(rng: &mut R) -> Self;
    fn is_zero(&self) -> bool;

    fn wrapping_add(self, other:Self) -> Self;
    fn wrapping_sub(self, other:Self) -> Self;
    fn wrapping_mul(self, other:Self) -> Self;

    #[inline]
    fn wrapping_div(self, other:Self) -> Self {
        self.wrapping_mul(other.checked_inv().expect("Division by zero"))
    }
    fn wrapping_neg(self) -> Self;
    fn square(self) -> Self;
    fn double(self) -> Self;
    fn checked_inv(self) -> Option<Self>;

    fn frobenius_map(self, power: usize) -> Self;

    fn pow<S: BitIterBE>(self, exp: S) -> Self {
        let mut res = Self::ONE;
        let mut found_one = false;
        for i in exp.bit_iter_be() {
            if found_one {
                res=res.square();
            } else {
                found_one = i;
            }
            if i {
                res = res.wrapping_mul(self);
            }
        }
        res
    }
}

pub trait SqrtField: Field {
    fn legendre(&self) -> LegendreSymbol;
    fn sqrt(&self) -> Option<Self>;
}

pub trait PrimeField: 
    PrimeFieldParams +
    SqrtField +
    std::str::FromStr +
    From<&'static str> +
    crate::borsh::BorshSerialize +
    crate::borsh::BorshDeserialize
{
    fn from_uint(v:Self::Inner) -> Option<Self>;
    fn from_mont_uint(v: Self::Inner) -> Option<Self>;
    fn from_uint_unchecked(v:Self::Inner) -> Self;
    fn from_mont_uint_unchecked(v: Self::Inner) -> Self;


    fn to_uint(&self) -> Self::Inner;
    fn to_mont_uint(&self) -> Self::Inner;
    fn as_mont_uint(&self) -> &Self::Inner;
    fn as_mont_uint_mut(&mut self) -> &mut Self::Inner;

    fn to_other<Fq:PrimeField>(&self) -> Option<Fq> {
        let u = self.to_uint().to_other()?;
        
        if u >= Fq::MODULUS {
            None
        } else {
            Some(Fq::from_uint_unchecked(u))
        }
    }

    fn to_other_reduced<Fq:PrimeField>(&self) -> Fq {
        match self.to_uint().to_other::<Fq::Inner>() {
            Some(u) => {
                Fq::from_uint_unchecked(u % Fq::MODULUS)
            },
            None => {
                let u = self.to_uint() % <Fq as PrimeFieldParams>::MODULUS.to_other().unwrap();
                Fq::from_uint_unchecked(u.to_other().unwrap())
            }
        }
    }
    

}
