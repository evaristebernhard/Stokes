use num_bigint::BigInt;
use num_rational::BigRational as NumBigRational;
use num_traits::{One, Zero};
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};
use std::str::FromStr;

pub const P3_VARIABLE_COUNT: usize = 4;
pub const AFFINE_P3_VARIABLE_COUNT: usize = 3;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ProjectiveSupport<const N: usize> {
    mask: u8,
}

impl<const N: usize> ProjectiveSupport<N> {
    pub fn new(mask: u8) -> Self {
        assert!(N > 0, "projective support needs at least one coordinate");
        assert!(
            N <= u8::BITS as usize,
            "projective support mask is u8-backed"
        );
        assert!(
            (1..(1usize << N)).contains(&usize::from(mask)),
            "support mask must be a nonempty subset of projective coordinates"
        );

        Self { mask }
    }

    pub fn mask(self) -> u8 {
        self.mask
    }

    pub fn chart_variable(self) -> usize {
        (0..N)
            .find(|&variable| self.contains_projective_variable(variable))
            .expect("support is nonempty")
    }

    pub fn contains_projective_variable(self, variable: usize) -> bool {
        assert!(variable < N, "projective variable index out of range");
        self.mask & (1 << variable) != 0
    }

    pub fn projective_variables(self) -> Vec<usize> {
        (0..N)
            .filter(|&variable| self.contains_projective_variable(variable))
            .collect()
    }
}

pub trait FieldElement:
    Clone
    + Eq
    + fmt::Debug
    + Add<Output = Self>
    + Div<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
    + Sub<Output = Self>
{
    fn zero() -> Self;

    fn one() -> Self;

    fn is_zero(&self) -> bool;

    fn pow_usize(&self, exponent: usize) -> Self {
        let mut result = Self::one();
        for _ in 0..exponent {
            result = result * self.clone();
        }
        result
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MonomialOrder {
    Lex,
    GrLex,
    GrevLex,
}

impl MonomialOrder {
    pub fn compare<const N: usize>(&self, lhs: &[usize; N], rhs: &[usize; N]) -> Ordering {
        match self {
            Self::Lex => compare_lex(lhs, rhs),
            Self::GrLex => compare_total_degree(lhs, rhs).then_with(|| compare_lex(lhs, rhs)),
            Self::GrevLex => compare_total_degree(lhs, rhs).then_with(|| compare_grevlex(lhs, rhs)),
        }
    }
}

impl FromStr for MonomialOrder {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        match value.to_ascii_lowercase().as_str() {
            "lex" => Ok(Self::Lex),
            "grlex" => Ok(Self::GrLex),
            "grevlex" => Ok(Self::GrevLex),
            _ => Err(format!("unknown monomial order `{value}`")),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparseTerm<T: FieldElement, const N: usize> {
    coefficient: T,
    exponents: [usize; N],
}

impl<T: FieldElement, const N: usize> SparseTerm<T, N> {
    pub fn coefficient(&self) -> T {
        self.coefficient.clone()
    }

    pub fn exponents(&self) -> [usize; N] {
        self.exponents
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SparsePolynomial<T: FieldElement, const N: usize> {
    terms: BTreeMap<[usize; N], T>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GroebnerCertificate<const N: usize, T: FieldElement = Rational> {
    order: MonomialOrder,
    generators: Vec<SparsePolynomial<T, N>>,
    basis: Vec<SparsePolynomial<T, N>>,
}

impl<const N: usize, T: FieldElement> GroebnerCertificate<N, T> {
    pub fn new(
        order: MonomialOrder,
        generators: Vec<SparsePolynomial<T, N>>,
        basis: Vec<SparsePolynomial<T, N>>,
    ) -> Self {
        assert!(
            !generators.is_empty(),
            "Groebner certificate needs generators"
        );
        assert!(
            !basis.is_empty(),
            "Groebner certificate needs a candidate basis"
        );

        Self {
            order,
            generators,
            basis,
        }
    }

    pub fn order(&self) -> MonomialOrder {
        self.order
    }

    pub fn generators(&self) -> &[SparsePolynomial<T, N>] {
        &self.generators
    }

    pub fn basis(&self) -> &[SparsePolynomial<T, N>] {
        &self.basis
    }

    pub fn verify(&self) -> GroebnerCertificateVerification {
        let basis_is_groebner = SparsePolynomial::is_groebner_basis(&self.basis, self.order);
        let generators_reduce_to_zero =
            SparsePolynomial::all_reduce_to_zero(&self.generators, &self.basis, self.order);

        GroebnerCertificateVerification {
            basis_is_groebner,
            generators_reduce_to_zero,
        }
    }

    pub fn standard_monomials(&self) -> Option<Vec<[usize; N]>> {
        SparsePolynomial::standard_monomials(&self.basis, self.order)
    }

    pub fn quotient_dimension(&self) -> Option<usize> {
        SparsePolynomial::quotient_dimension(&self.basis, self.order)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct GroebnerCertificateVerification {
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
}

impl GroebnerCertificateVerification {
    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn verified(self) -> bool {
        self.basis_is_groebner && self.generators_reduce_to_zero
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GroebnerLiftCertificate<const N: usize, T: FieldElement = BigQuadraticRational> {
    source_count: usize,
    coefficients: Vec<Vec<SparsePolynomial<T, N>>>,
}

impl<const N: usize, T: FieldElement> GroebnerLiftCertificate<N, T> {
    pub fn new(source_count: usize, coefficients: Vec<Vec<SparsePolynomial<T, N>>>) -> Self {
        assert!(
            coefficients
                .iter()
                .all(|target_coefficients| target_coefficients.len() == source_count),
            "each lift target needs one coefficient polynomial per source"
        );

        Self {
            source_count,
            coefficients,
        }
    }

    pub fn source_count(&self) -> usize {
        self.source_count
    }

    pub fn target_count(&self) -> usize {
        self.coefficients.len()
    }

    pub fn coefficients(&self) -> &[Vec<SparsePolynomial<T, N>>] {
        &self.coefficients
    }

    pub fn verifies_targets(
        &self,
        generators: &[SparsePolynomial<T, N>],
        targets: &[SparsePolynomial<T, N>],
    ) -> bool {
        if self.source_count != generators.len() || self.coefficients.len() != targets.len() {
            return false;
        }

        self.coefficients
            .iter()
            .zip(targets)
            .all(|(target_coefficients, target)| {
                if target_coefficients.len() != generators.len() {
                    return false;
                }

                let reconstructed = target_coefficients
                    .iter()
                    .zip(generators)
                    .fold(SparsePolynomial::zero(), |sum, (coefficient, generator)| {
                        sum.add(&coefficient.mul(generator))
                    });
                reconstructed == *target
            })
    }

    pub fn verifies_mapped_targets<U: FieldElement>(
        &self,
        generators: &[SparsePolynomial<U, N>],
        targets: &[SparsePolynomial<U, N>],
        mut map_polynomial: impl FnMut(&SparsePolynomial<U, N>) -> SparsePolynomial<T, N>,
    ) -> bool {
        if self.source_count != generators.len() || self.coefficients.len() != targets.len() {
            return false;
        }

        let mapped_generators = generators
            .iter()
            .map(&mut map_polynomial)
            .collect::<Vec<_>>();
        let mapped_targets = targets.iter().map(&mut map_polynomial).collect::<Vec<_>>();

        self.verifies_targets(&mapped_generators, &mapped_targets)
    }
}

impl<const N: usize> GroebnerLiftCertificate<N, BigQuadraticRational> {
    pub fn verifies_quadratic_targets(
        &self,
        generators: &[SparsePolynomial<QuadraticRational, N>],
        targets: &[SparsePolynomial<QuadraticRational, N>],
    ) -> bool {
        self.verifies_mapped_targets(generators, targets, |polynomial| {
            polynomial.map_coefficients(|coefficient| BigQuadraticRational::from(*coefficient))
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct GroebnerCertificateParseError {
    line: usize,
    message: String,
}

impl GroebnerCertificateParseError {
    pub fn line(&self) -> usize {
        self.line
    }

    pub fn message(&self) -> &str {
        &self.message
    }
}

impl fmt::Display for GroebnerCertificateParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.line == 0 {
            write!(f, "{}", self.message)
        } else {
            write!(f, "line {}: {}", self.line, self.message)
        }
    }
}

impl std::error::Error for GroebnerCertificateParseError {}

impl<T: FieldElement, const N: usize> SparsePolynomial<T, N> {
    pub fn zero() -> Self {
        Self {
            terms: BTreeMap::new(),
        }
    }

    pub fn constant(coefficient: T) -> Self {
        Self::from_terms(vec![(coefficient, [0; N])])
    }

    pub fn variable(variable: usize) -> Self {
        assert!(variable < N, "polynomial variable index out of range");
        let mut exponents = [0; N];
        exponents[variable] = 1;

        Self::from_terms(vec![(T::one(), exponents)])
    }

    pub fn from_terms(terms: Vec<(T, [usize; N])>) -> Self {
        let mut combined = BTreeMap::<[usize; N], T>::new();

        for (coefficient, exponents) in terms {
            if coefficient.is_zero() {
                continue;
            }

            let entry = combined.entry(exponents).or_insert_with(T::zero);
            *entry = entry.clone() + coefficient;
        }

        combined.retain(|_, coefficient| !coefficient.is_zero());

        Self { terms: combined }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn terms(&self) -> Vec<SparseTerm<T, N>> {
        self.terms
            .iter()
            .map(|(&exponents, coefficient)| SparseTerm {
                coefficient: coefficient.clone(),
                exponents,
            })
            .collect()
    }

    pub fn coefficient(&self, exponents: &[usize; N]) -> T {
        self.terms.get(exponents).cloned().unwrap_or_else(T::zero)
    }

    pub fn map_coefficients<U: FieldElement>(
        &self,
        mut map: impl FnMut(&T) -> U,
    ) -> SparsePolynomial<U, N> {
        SparsePolynomial::from_terms(
            self.terms
                .iter()
                .map(|(&exponents, coefficient)| (map(coefficient), exponents))
                .collect(),
        )
    }

    pub fn degree(&self) -> usize {
        self.terms.keys().map(monomial_degree_n).max().unwrap_or(0)
    }

    pub fn is_homogeneous(&self) -> bool {
        let mut degrees = self.terms.keys().map(monomial_degree_n);
        let Some(first_degree) = degrees.next() else {
            return true;
        };

        degrees.all(|degree| degree == first_degree)
    }

    pub fn evaluate(&self, coords: &[T; N]) -> T {
        self.terms
            .iter()
            .map(|(&exponents, coefficient)| {
                evaluate_sparse_term(coefficient.clone(), &exponents, coords)
            })
            .fold(T::zero(), |sum, value| sum + value)
    }

    pub fn partial_derivative(&self, variable: usize) -> Self {
        assert!(
            variable < N,
            "partial derivative variable index out of range"
        );

        Self::from_terms(
            self.terms
                .iter()
                .filter_map(|(&exponents, coefficient)| {
                    let exponent = exponents[variable];
                    if exponent == 0 {
                        return None;
                    }

                    let mut derivative_exponents = exponents;
                    derivative_exponents[variable] -= 1;

                    Some((
                        coefficient.clone() * repeated_one::<T>(exponent),
                        derivative_exponents,
                    ))
                })
                .collect(),
        )
    }

    pub fn add(&self, rhs: &Self) -> Self {
        let mut terms: Vec<_> = self
            .terms
            .iter()
            .map(|(&exponents, coefficient)| (coefficient.clone(), exponents))
            .collect();
        terms.extend(
            rhs.terms
                .iter()
                .map(|(&exponents, coefficient)| (coefficient.clone(), exponents)),
        );

        Self::from_terms(terms)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        self.add(&rhs.scale(-T::one()))
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        let mut terms = Vec::new();

        for (&left_exponents, left_coefficient) in &self.terms {
            for (&right_exponents, right_coefficient) in &rhs.terms {
                let exponents =
                    std::array::from_fn(|index| left_exponents[index] + right_exponents[index]);
                terms.push((
                    left_coefficient.clone() * right_coefficient.clone(),
                    exponents,
                ));
            }
        }

        Self::from_terms(terms)
    }

    pub fn scale(&self, scalar: T) -> Self {
        Self::from_terms(
            self.terms
                .iter()
                .map(|(&exponents, coefficient)| (scalar.clone() * coefficient.clone(), exponents))
                .collect(),
        )
    }

    pub fn pow_usize(&self, exponent: usize) -> Self {
        (0..exponent).fold(Self::constant(T::one()), |value, _| value.mul(self))
    }

    pub fn mul_monomial(&self, coefficient: T, exponents: [usize; N]) -> Self {
        Self::from_terms(
            self.terms
                .iter()
                .map(|(&term_exponents, term_coefficient)| {
                    let product_exponents =
                        std::array::from_fn(|index| term_exponents[index] + exponents[index]);
                    (
                        coefficient.clone() * term_coefficient.clone(),
                        product_exponents,
                    )
                })
                .collect(),
        )
    }

    pub fn leading_term(&self, order: MonomialOrder) -> Option<SparseTerm<T, N>> {
        self.terms
            .iter()
            .max_by(|(lhs_exponents, _), (rhs_exponents, _)| {
                order.compare(lhs_exponents, rhs_exponents)
            })
            .map(|(&exponents, coefficient)| SparseTerm {
                coefficient: coefficient.clone(),
                exponents,
            })
    }

    pub fn leading_monomials(basis: &[Self], order: MonomialOrder) -> Vec<[usize; N]> {
        basis
            .iter()
            .filter_map(|polynomial| polynomial.leading_term(order))
            .map(|term| term.exponents())
            .collect()
    }

    pub fn normal_form(&self, basis: &[Self], order: MonomialOrder) -> Self {
        let mut remainder = Self::zero();
        let mut dividend = self.clone();

        while let Some(leading_dividend) = dividend.leading_term(order) {
            let reducer = basis.iter().find_map(|basis_polynomial| {
                let leading_basis = basis_polynomial.leading_term(order)?;
                monomial_quotient(&leading_dividend.exponents, &leading_basis.exponents).map(
                    |quotient_exponents| {
                        (
                            basis_polynomial,
                            leading_dividend.coefficient.clone() / leading_basis.coefficient,
                            quotient_exponents,
                        )
                    },
                )
            });

            if let Some((basis_polynomial, quotient_coefficient, quotient_exponents)) = reducer {
                let reduction =
                    basis_polynomial.mul_monomial(quotient_coefficient, quotient_exponents);
                dividend = dividend.sub(&reduction);
            } else {
                let leading_term = Self::from_terms(vec![(
                    leading_dividend.coefficient.clone(),
                    leading_dividend.exponents,
                )]);
                remainder = remainder.add(&leading_term);
                dividend = dividend.sub(&leading_term);
            }
        }

        remainder
    }

    pub fn s_polynomial(&self, rhs: &Self, order: MonomialOrder) -> Option<Self> {
        let lhs_leading = self.leading_term(order)?;
        let rhs_leading = rhs.leading_term(order)?;
        let lcm_exponents = monomial_lcm(&lhs_leading.exponents, &rhs_leading.exponents);
        let lhs_multiplier = monomial_quotient(&lcm_exponents, &lhs_leading.exponents)
            .expect("leading monomial must divide the lcm");
        let rhs_multiplier = monomial_quotient(&lcm_exponents, &rhs_leading.exponents)
            .expect("leading monomial must divide the lcm");

        Some(
            self.mul_monomial(T::one() / lhs_leading.coefficient, lhs_multiplier)
                .sub(&rhs.mul_monomial(T::one() / rhs_leading.coefficient, rhs_multiplier)),
        )
    }

    pub fn all_reduce_to_zero(polynomials: &[Self], basis: &[Self], order: MonomialOrder) -> bool {
        polynomials
            .iter()
            .all(|polynomial| polynomial.normal_form(basis, order).is_zero())
    }

    pub fn is_groebner_basis(basis: &[Self], order: MonomialOrder) -> bool {
        if basis.iter().any(Self::is_zero) {
            return false;
        }

        for lhs_index in 0..basis.len() {
            for rhs_index in (lhs_index + 1)..basis.len() {
                let s_polynomial = basis[lhs_index]
                    .s_polynomial(&basis[rhs_index], order)
                    .expect("nonzero basis polynomials have an S-polynomial");
                if !s_polynomial.normal_form(basis, order).is_zero() {
                    return false;
                }
            }
        }

        true
    }

    pub fn standard_monomials(basis: &[Self], order: MonomialOrder) -> Option<Vec<[usize; N]>> {
        let leading_monomials = Self::leading_monomials(basis, order);
        if leading_monomials.iter().any(|monomial| monomial == &[0; N]) {
            return Some(Vec::new());
        }

        let bounds = standard_monomial_bounds(&leading_monomials)?;
        let mut standard_monomials = Vec::new();
        let mut current = [0; N];

        enumerate_exponents_below_bounds(&bounds, &mut current, 0, &mut |exponents| {
            if !leading_monomials
                .iter()
                .any(|leading| monomial_divides(leading, exponents))
            {
                standard_monomials.push(*exponents);
            }
        });

        Some(standard_monomials)
    }

    pub fn quotient_dimension(basis: &[Self], order: MonomialOrder) -> Option<usize> {
        Self::standard_monomials(basis, order).map(|monomials| monomials.len())
    }
}

impl<const N: usize, T> FromStr for GroebnerCertificate<N, T>
where
    T: FieldElement + FromStr,
    <T as FromStr>::Err: fmt::Display,
{
    type Err = GroebnerCertificateParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        parse_groebner_certificate(input)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct Rational {
    num: i128,
    den: i128,
}

impl FromStr for Rational {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.trim();
        if value.is_empty() {
            return Err("empty rational".to_string());
        }

        if let Some((numerator, denominator)) = value.split_once('/') {
            let numerator = numerator
                .parse::<i128>()
                .map_err(|error| format!("invalid rational numerator `{numerator}`: {error}"))?;
            let denominator = denominator.parse::<i128>().map_err(|error| {
                format!("invalid rational denominator `{denominator}`: {error}")
            })?;
            if denominator == 0 {
                return Err("rational denominator cannot be zero".to_string());
            }
            Ok(Self::new(numerator, denominator))
        } else {
            value
                .parse::<i128>()
                .map(|numerator| Self::new(numerator, 1))
                .map_err(|error| format!("invalid rational `{value}`: {error}"))
        }
    }
}

impl Rational {
    pub const ZERO: Self = Self { num: 0, den: 1 };
    pub const ONE: Self = Self { num: 1, den: 1 };

    pub fn new(num: i128, den: i128) -> Self {
        assert!(den != 0, "rational denominator cannot be zero");
        if num == 0 {
            return Self::ZERO;
        }

        let sign = if den < 0 { -1 } else { 1 };
        let gcd = gcd_i128(num.abs(), den.abs());
        Self {
            num: sign * num / gcd,
            den: den.abs() / gcd,
        }
    }

    pub fn from_i64(value: i64) -> Self {
        Self::new(value as i128, 1)
    }

    pub fn is_zero(self) -> bool {
        self.num == 0
    }

    pub fn numerator(self) -> i128 {
        self.num
    }

    pub fn denominator(self) -> i128 {
        self.den
    }

    pub fn pow_usize(self, exponent: usize) -> Self {
        FieldElement::pow_usize(&self, exponent)
    }
}

impl FieldElement for Rational {
    fn zero() -> Self {
        Self::ZERO
    }

    fn one() -> Self {
        Self::ONE
    }

    fn is_zero(&self) -> bool {
        self.num == 0
    }
}

impl From<i64> for Rational {
    fn from(value: i64) -> Self {
        Self::from_i64(value)
    }
}

impl Add for Rational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.num * rhs.den + rhs.num * self.den, self.den * rhs.den)
    }
}

impl Sub for Rational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Mul for Rational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.num * rhs.num, self.den * rhs.den)
    }
}

impl Div for Rational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        assert!(!rhs.is_zero(), "cannot divide by zero rational");
        Self::new(self.num * rhs.den, self.den * rhs.num)
    }
}

impl Neg for Rational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            num: -self.num,
            den: self.den,
        }
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.den == 1 {
            write!(f, "{}", self.num)
        } else {
            write!(f, "{}/{}", self.num, self.den)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct BigRational {
    value: NumBigRational,
}

impl BigRational {
    pub fn new(numerator: BigInt, denominator: BigInt) -> Self {
        assert!(
            !denominator.is_zero(),
            "big rational denominator cannot be zero"
        );
        Self {
            value: NumBigRational::new(numerator, denominator),
        }
    }

    pub fn from_i64(value: i64) -> Self {
        Self {
            value: NumBigRational::from_integer(BigInt::from(value)),
        }
    }

    pub fn numerator(&self) -> &BigInt {
        self.value.numer()
    }

    pub fn denominator(&self) -> &BigInt {
        self.value.denom()
    }

    pub fn is_zero(&self) -> bool {
        self.value.is_zero()
    }

    pub fn pow_usize(&self, exponent: usize) -> Self {
        FieldElement::pow_usize(self, exponent)
    }
}

impl FromStr for BigRational {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let value = value.trim();
        if value.is_empty() {
            return Err("empty big rational".to_string());
        }

        if let Some((numerator, denominator)) = value.split_once('/') {
            let numerator = numerator.parse::<BigInt>().map_err(|error| {
                format!("invalid big rational numerator `{numerator}`: {error}")
            })?;
            let denominator = denominator.parse::<BigInt>().map_err(|error| {
                format!("invalid big rational denominator `{denominator}`: {error}")
            })?;
            if denominator.is_zero() {
                return Err("big rational denominator cannot be zero".to_string());
            }
            Ok(Self::new(numerator, denominator))
        } else {
            value
                .parse::<BigInt>()
                .map(|numerator| Self::new(numerator, BigInt::one()))
                .map_err(|error| format!("invalid big rational `{value}`: {error}"))
        }
    }
}

impl FieldElement for BigRational {
    fn zero() -> Self {
        Self::from_i64(0)
    }

    fn one() -> Self {
        Self::from_i64(1)
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }
}

impl From<i64> for BigRational {
    fn from(value: i64) -> Self {
        Self::from_i64(value)
    }
}

impl From<Rational> for BigRational {
    fn from(value: Rational) -> Self {
        Self::new(
            BigInt::from(value.numerator()),
            BigInt::from(value.denominator()),
        )
    }
}

impl Add for BigRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value + rhs.value,
        }
    }
}

impl Sub for BigRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value - rhs.value,
        }
    }
}

impl Mul for BigRational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            value: self.value * rhs.value,
        }
    }
}

impl Div for BigRational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        assert!(!rhs.value.is_zero(), "cannot divide by zero big rational");
        Self {
            value: self.value / rhs.value,
        }
    }
}

impl Neg for BigRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self { value: -self.value }
    }
}

impl fmt::Display for BigRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.value.is_integer() {
            write!(f, "{}", self.value.to_integer())
        } else {
            write!(f, "{}/{}", self.value.numer(), self.value.denom())
        }
    }
}

#[derive(Clone, Debug)]
pub struct BigQuadraticRational {
    rational: BigRational,
    irrational: BigRational,
    radicand: i64,
}

impl BigQuadraticRational {
    pub fn new(rational: BigRational, irrational: BigRational, radicand: i64) -> Self {
        if irrational.is_zero() {
            return Self {
                rational,
                irrational: BigRational::from_i64(0),
                radicand: 0,
            };
        }

        assert!(radicand > 0, "quadratic radicand must be positive");
        Self {
            rational,
            irrational,
            radicand,
        }
    }

    pub fn from_rational(rational: BigRational) -> Self {
        Self::new(rational, BigRational::from_i64(0), 0)
    }

    pub fn from_i64(value: i64) -> Self {
        Self::from_rational(BigRational::from_i64(value))
    }

    pub fn is_zero(&self) -> bool {
        self.rational.is_zero() && self.irrational.is_zero()
    }

    fn common_radicand(&self, rhs: &Self) -> i64 {
        match (
            self.irrational.is_zero(),
            rhs.irrational.is_zero(),
            self.radicand,
            rhs.radicand,
        ) {
            (true, true, _, _) => 0,
            (true, false, _, radicand) | (false, true, radicand, _) => radicand,
            (false, false, lhs, rhs) => {
                assert_eq!(lhs, rhs, "quadratic radicands must match");
                lhs
            }
        }
    }

    fn with_radicand(self, radicand: i64) -> Self {
        if self.irrational.is_zero() {
            Self {
                rational: self.rational,
                irrational: BigRational::from_i64(0),
                radicand: 0,
            }
        } else {
            assert_eq!(self.radicand, radicand, "quadratic radicands must match");
            self
        }
    }
}

impl From<QuadraticRational> for BigQuadraticRational {
    fn from(value: QuadraticRational) -> Self {
        Self::new(
            BigRational::from(value.rational()),
            BigRational::from(value.irrational()),
            value.radicand(),
        )
    }
}

impl From<i64> for BigQuadraticRational {
    fn from(value: i64) -> Self {
        Self::from_i64(value)
    }
}

impl PartialEq for BigQuadraticRational {
    fn eq(&self, rhs: &Self) -> bool {
        self.rational == rhs.rational
            && self.irrational == rhs.irrational
            && (self.irrational.is_zero() || self.radicand == rhs.radicand)
    }
}

impl Eq for BigQuadraticRational {}

impl Add for BigQuadraticRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let radicand = self.common_radicand(&rhs);
        let lhs = self.with_radicand(radicand);
        let rhs = rhs.with_radicand(radicand);
        Self::new(
            lhs.rational + rhs.rational,
            lhs.irrational + rhs.irrational,
            radicand,
        )
    }
}

impl Sub for BigQuadraticRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Mul for BigQuadraticRational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let radicand = self.common_radicand(&rhs);
        let lhs = self.with_radicand(radicand);
        let rhs = rhs.with_radicand(radicand);
        let radicand_value = BigRational::from_i64(radicand);

        Self::new(
            lhs.rational.clone() * rhs.rational.clone()
                + lhs.irrational.clone() * rhs.irrational.clone() * radicand_value,
            lhs.rational * rhs.irrational + lhs.irrational * rhs.rational,
            radicand,
        )
    }
}

impl Div for BigQuadraticRational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        assert!(!rhs.is_zero(), "cannot divide by zero quadratic rational");
        if rhs.irrational.is_zero() {
            return Self::new(
                self.rational / rhs.rational.clone(),
                self.irrational / rhs.rational,
                self.radicand,
            );
        }

        let radicand = self.common_radicand(&rhs);
        let rhs = rhs.with_radicand(radicand);
        let conjugate = Self::new(rhs.rational.clone(), -rhs.irrational.clone(), radicand);
        let numerator = self * conjugate;
        let denominator = rhs.rational.clone() * rhs.rational
            - rhs.irrational.clone() * rhs.irrational * BigRational::from_i64(radicand);

        Self::new(
            numerator.rational / denominator.clone(),
            numerator.irrational / denominator,
            numerator.radicand,
        )
    }
}

impl Neg for BigQuadraticRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.rational, -self.irrational, self.radicand)
    }
}

impl FieldElement for BigQuadraticRational {
    fn zero() -> Self {
        Self::from_i64(0)
    }

    fn one() -> Self {
        Self::from_i64(1)
    }

    fn is_zero(&self) -> bool {
        self.is_zero()
    }
}

impl FromStr for BigQuadraticRational {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        parse_big_quadratic_rational_sqrt5(value)
    }
}

fn parse_big_quadratic_rational_sqrt5(value: &str) -> Result<BigQuadraticRational, String> {
    let value = value.trim();
    if value.is_empty() {
        return Err("empty quadratic rational".to_string());
    }

    let owned_value = value.replace('*', "");
    let value = owned_value
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))
        .unwrap_or(&owned_value);
    if !value.contains('t') {
        return value
            .parse::<BigRational>()
            .map(BigQuadraticRational::from_rational);
    }

    let mut rational = BigRational::from_i64(0);
    let mut irrational = BigRational::from_i64(0);
    for term in split_signed_terms(value) {
        if let Some(coefficient) = term.strip_suffix('t') {
            let coefficient = match coefficient {
                "" | "+" => BigRational::from_i64(1),
                "-" => -BigRational::from_i64(1),
                _ => coefficient.parse::<BigRational>()?,
            };
            irrational = irrational + coefficient;
        } else {
            rational = rational + term.parse::<BigRational>()?;
        }
    }

    Ok(BigQuadraticRational::new(rational, irrational, 5))
}

#[derive(Clone, Copy, Debug)]
pub struct QuadraticRational {
    rational: Rational,
    irrational: Rational,
    radicand: i64,
}

impl QuadraticRational {
    pub const ZERO: Self = Self {
        rational: Rational::ZERO,
        irrational: Rational::ZERO,
        radicand: 0,
    };
    pub const ONE: Self = Self {
        rational: Rational::ONE,
        irrational: Rational::ZERO,
        radicand: 0,
    };

    pub fn new(rational: Rational, irrational: Rational, radicand: i64) -> Self {
        if irrational.is_zero() {
            return Self {
                rational,
                irrational: Rational::ZERO,
                radicand: 0,
            };
        }

        assert!(radicand > 0, "quadratic radicand must be positive");
        Self {
            rational,
            irrational,
            radicand,
        }
    }

    pub fn from_rational(rational: Rational) -> Self {
        Self::new(rational, Rational::ZERO, 0)
    }

    pub fn from_i64(value: i64) -> Self {
        Self::from_rational(Rational::from_i64(value))
    }

    pub fn sqrt(radicand: i64) -> Self {
        Self::new(Rational::ZERO, Rational::ONE, radicand)
    }

    pub fn rational(self) -> Rational {
        self.rational
    }

    pub fn irrational(self) -> Rational {
        self.irrational
    }

    pub fn radicand(self) -> i64 {
        self.radicand
    }

    pub fn is_zero(self) -> bool {
        self.rational.is_zero() && self.irrational.is_zero()
    }

    fn common_radicand(self, rhs: Self) -> i64 {
        match (
            self.irrational.is_zero(),
            rhs.irrational.is_zero(),
            self.radicand,
            rhs.radicand,
        ) {
            (true, true, _, _) => 0,
            (true, false, _, radicand) | (false, true, radicand, _) => radicand,
            (false, false, lhs, rhs) => {
                assert_eq!(lhs, rhs, "quadratic radicands must match");
                lhs
            }
        }
    }

    fn with_radicand(self, radicand: i64) -> Self {
        if self.irrational.is_zero() {
            Self {
                rational: self.rational,
                irrational: Rational::ZERO,
                radicand: 0,
            }
        } else {
            assert_eq!(self.radicand, radicand, "quadratic radicands must match");
            self
        }
    }
}

impl From<i64> for QuadraticRational {
    fn from(value: i64) -> Self {
        Self::from_i64(value)
    }
}

impl PartialEq for QuadraticRational {
    fn eq(&self, rhs: &Self) -> bool {
        self.rational == rhs.rational
            && self.irrational == rhs.irrational
            && (self.irrational.is_zero() || self.radicand == rhs.radicand)
    }
}

impl Eq for QuadraticRational {}

impl Add for QuadraticRational {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        let radicand = self.common_radicand(rhs);
        let lhs = self.with_radicand(radicand);
        let rhs = rhs.with_radicand(radicand);
        Self::new(
            lhs.rational + rhs.rational,
            lhs.irrational + rhs.irrational,
            radicand,
        )
    }
}

impl Sub for QuadraticRational {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        self + (-rhs)
    }
}

impl Mul for QuadraticRational {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        let radicand = self.common_radicand(rhs);
        let lhs = self.with_radicand(radicand);
        let rhs = rhs.with_radicand(radicand);
        let radicand_value = Rational::from_i64(radicand);

        Self::new(
            lhs.rational * rhs.rational + lhs.irrational * rhs.irrational * radicand_value,
            lhs.rational * rhs.irrational + lhs.irrational * rhs.rational,
            radicand,
        )
    }
}

impl Div for QuadraticRational {
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        assert!(!rhs.is_zero(), "cannot divide by zero quadratic rational");
        if rhs.irrational.is_zero() {
            return Self::new(
                self.rational / rhs.rational,
                self.irrational / rhs.rational,
                self.radicand,
            );
        }

        let radicand = self.common_radicand(rhs);
        let rhs = rhs.with_radicand(radicand);
        let conjugate = Self::new(rhs.rational, -rhs.irrational, radicand);
        let numerator = self * conjugate;
        let denominator = rhs.rational * rhs.rational
            - rhs.irrational * rhs.irrational * Rational::from_i64(radicand);

        Self::new(
            numerator.rational / denominator,
            numerator.irrational / denominator,
            numerator.radicand,
        )
    }
}

impl Neg for QuadraticRational {
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self::new(-self.rational, -self.irrational, self.radicand)
    }
}

impl FieldElement for QuadraticRational {
    fn zero() -> Self {
        Self::ZERO
    }

    fn one() -> Self {
        Self::ONE
    }

    fn is_zero(&self) -> bool {
        self.rational.is_zero() && self.irrational.is_zero()
    }
}

impl FromStr for QuadraticRational {
    type Err = String;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        parse_quadratic_rational_sqrt5(value)
    }
}

impl fmt::Display for QuadraticRational {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.irrational.is_zero() {
            return write!(f, "{}", self.rational);
        }

        if self.rational.is_zero() {
            if self.irrational < Rational::ZERO {
                write!(f, "-")?;
                return write_quadratic_irrational_part(f, -self.irrational, self.radicand);
            }
            return write_quadratic_irrational_part(f, self.irrational, self.radicand);
        }

        write!(f, "{}", self.rational)?;
        if self.irrational < Rational::ZERO {
            write!(f, " - ")?;
            write_quadratic_irrational_part(f, -self.irrational, self.radicand)
        } else {
            write!(f, " + ")?;
            write_quadratic_irrational_part(f, self.irrational, self.radicand)
        }
    }
}

fn parse_quadratic_rational_sqrt5(value: &str) -> Result<QuadraticRational, String> {
    let value = value.trim();
    if value.is_empty() {
        return Err("empty quadratic rational".to_string());
    }

    let owned_value = value.replace('*', "");
    let value = owned_value
        .strip_prefix('(')
        .and_then(|inner| inner.strip_suffix(')'))
        .unwrap_or(&owned_value);
    if !value.contains('t') {
        return value
            .parse::<Rational>()
            .map(QuadraticRational::from_rational);
    }

    let mut rational = Rational::ZERO;
    let mut irrational = Rational::ZERO;
    for term in split_signed_terms(value) {
        if let Some(coefficient) = term.strip_suffix('t') {
            let coefficient = match coefficient {
                "" | "+" => Rational::ONE,
                "-" => -Rational::ONE,
                _ => coefficient.parse::<Rational>()?,
            };
            irrational = irrational + coefficient;
        } else {
            rational = rational + term.parse::<Rational>()?;
        }
    }

    Ok(QuadraticRational::new(rational, irrational, 5))
}

fn split_signed_terms(value: &str) -> Vec<&str> {
    let mut terms = Vec::new();
    let mut start = 0;
    for (index, character) in value.char_indices().skip(1) {
        if character == '+' || character == '-' {
            terms.push(&value[start..index]);
            start = index;
        }
    }
    terms.push(&value[start..]);
    terms
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ProjectivePoint<T: FieldElement = Rational> {
    coords: Vec<T>,
}

impl<T: FieldElement> ProjectivePoint<T> {
    pub fn new(coords: Vec<T>) -> Self {
        assert!(
            coords.iter().any(|coord| !coord.is_zero()),
            "projective point cannot be the zero vector"
        );
        Self {
            coords: normalize_projective(coords),
        }
    }

    pub fn coords(&self) -> &[T] {
        &self.coords
    }

    pub fn p3_coords(&self) -> [T; P3_VARIABLE_COUNT] {
        assert_eq!(
            self.coords.len(),
            P3_VARIABLE_COUNT,
            "expected a point in P^3"
        );
        [
            self.coords[0].clone(),
            self.coords[1].clone(),
            self.coords[2].clone(),
            self.coords[3].clone(),
        ]
    }
}

impl<T: FieldElement + fmt::Display> fmt::Display for ProjectivePoint<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (index, coord) in self.coords.iter().enumerate() {
            if index > 0 {
                write!(f, ":")?;
            }
            write!(f, "{coord}")?;
        }
        write!(f, "]")
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Matrix<T: FieldElement = Rational> {
    rows: usize,
    cols: usize,
    data: Vec<T>,
}

impl<T: FieldElement> Matrix<T> {
    pub fn from_rows(rows: Vec<Vec<T>>) -> Self {
        assert!(!rows.is_empty(), "matrix must have at least one row");
        let cols = rows[0].len();
        assert!(cols > 0, "matrix must have at least one column");
        assert!(
            rows.iter().all(|row| row.len() == cols),
            "matrix rows must have equal length"
        );

        let row_count = rows.len();
        let data = rows.into_iter().flatten().collect();
        Self {
            rows: row_count,
            cols,
            data,
        }
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn cols(&self) -> usize {
        self.cols
    }

    pub fn get(&self, row: usize, col: usize) -> T {
        self.data[row * self.cols + col].clone()
    }

    pub fn rank(&self) -> usize {
        self.rref().pivots.len()
    }

    pub fn nullspace(&self) -> Vec<Vec<T>> {
        let rref = self.rref();
        let mut is_pivot_col = vec![false; self.cols];
        for &pivot in &rref.pivots {
            is_pivot_col[pivot] = true;
        }

        let free_cols: Vec<usize> = (0..self.cols).filter(|&col| !is_pivot_col[col]).collect();
        let mut basis = Vec::with_capacity(free_cols.len());

        for free_col in free_cols {
            let mut vector = vec![T::zero(); self.cols];
            vector[free_col] = T::one();

            for (pivot_row, &pivot_col) in rref.pivots.iter().enumerate() {
                vector[pivot_col] = -rref.matrix[pivot_row][free_col].clone();
            }

            basis.push(vector);
        }

        basis
    }

    fn rref(&self) -> Rref<T> {
        let mut matrix = vec![vec![T::zero(); self.cols]; self.rows];
        for (row, matrix_row) in matrix.iter_mut().enumerate() {
            for (col, entry) in matrix_row.iter_mut().enumerate() {
                *entry = self.get(row, col);
            }
        }

        let mut pivots = Vec::new();
        let mut pivot_row = 0;

        for col in 0..self.cols {
            let Some(row_with_pivot) =
                (pivot_row..self.rows).find(|&row| !matrix[row][col].is_zero())
            else {
                continue;
            };

            matrix.swap(pivot_row, row_with_pivot);
            let pivot = matrix[pivot_row][col].clone();
            for entry in &mut matrix[pivot_row] {
                *entry = entry.clone() / pivot.clone();
            }

            let pivot_values = matrix[pivot_row].clone();
            for (row, matrix_row) in matrix.iter_mut().enumerate() {
                if row == pivot_row {
                    continue;
                }
                let factor = matrix_row[col].clone();
                if factor.is_zero() {
                    continue;
                }

                for (entry, pivot_entry) in matrix_row.iter_mut().zip(&pivot_values) {
                    *entry = entry.clone() - factor.clone() * pivot_entry.clone();
                }
            }

            pivots.push(col);
            pivot_row += 1;
            if pivot_row == self.rows {
                break;
            }
        }

        Rref { matrix, pivots }
    }
}

struct Rref<T: FieldElement> {
    matrix: Vec<Vec<T>>,
    pivots: Vec<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct HomogeneousPolynomialP3<T: FieldElement = Rational> {
    terms: Vec<MonomialP3<T>>,
    degree: usize,
}

impl<T: FieldElement> HomogeneousPolynomialP3<T> {
    pub fn from_terms(terms: Vec<(T, [usize; P3_VARIABLE_COUNT])>) -> Self {
        let degree = terms
            .iter()
            .find(|(coefficient, _)| !coefficient.is_zero())
            .map(|(_, exponents)| monomial_degree(exponents))
            .unwrap_or(0);

        let mut combined = BTreeMap::<[usize; P3_VARIABLE_COUNT], T>::new();
        for (coefficient, exponents) in terms {
            if coefficient.is_zero() {
                continue;
            }

            assert_eq!(
                monomial_degree(&exponents),
                degree,
                "all terms in a homogeneous polynomial must have equal degree"
            );

            let entry = combined.entry(exponents).or_insert_with(T::zero);
            *entry = entry.clone() + coefficient;
        }

        let terms: Vec<_> = combined
            .into_iter()
            .filter_map(|(exponents, coefficient)| {
                (!coefficient.is_zero()).then_some(MonomialP3 {
                    coefficient,
                    exponents,
                })
            })
            .collect();
        let degree = if terms.is_empty() { 0 } else { degree };

        Self { terms, degree }
    }

    pub fn degree(&self) -> usize {
        self.degree
    }

    pub fn terms(&self) -> &[MonomialP3<T>] {
        &self.terms
    }

    pub fn to_sparse(&self) -> SparsePolynomial<T, P3_VARIABLE_COUNT> {
        SparsePolynomial::from_terms(
            self.terms
                .iter()
                .map(|term| (term.coefficient.clone(), term.exponents))
                .collect(),
        )
    }

    pub fn dehomogenize(
        &self,
        chart_variable: usize,
    ) -> SparsePolynomial<T, AFFINE_P3_VARIABLE_COUNT> {
        dehomogenize_p3_sparse(&self.to_sparse(), chart_variable)
    }

    pub fn affine_singular_generators(
        &self,
        chart_variable: usize,
    ) -> Vec<SparsePolynomial<T, AFFINE_P3_VARIABLE_COUNT>> {
        affine_hypersurface_singular_generators_p3(self, chart_variable)
    }

    pub fn evaluate(&self, coords: &[T; P3_VARIABLE_COUNT]) -> T {
        self.terms
            .iter()
            .map(|term| term.evaluate(coords))
            .fold(T::zero(), |sum, value| sum + value)
    }

    pub fn partial_derivative(&self, variable: usize) -> Self {
        assert!(
            variable < P3_VARIABLE_COUNT,
            "partial derivative variable index out of range"
        );

        let terms = self
            .terms
            .iter()
            .filter_map(|term| term.partial_derivative(variable))
            .map(|term| (term.coefficient, term.exponents))
            .collect();

        Self::from_terms(terms)
    }

    pub fn gradient_at(&self, coords: &[T; P3_VARIABLE_COUNT]) -> [T; P3_VARIABLE_COUNT] {
        std::array::from_fn(|variable| self.partial_derivative(variable).evaluate(coords))
    }

    pub fn hessian_at(&self, coords: &[T; P3_VARIABLE_COUNT]) -> Matrix<T> {
        Matrix::from_rows(
            (0..P3_VARIABLE_COUNT)
                .map(|row| {
                    let first = self.partial_derivative(row);
                    (0..P3_VARIABLE_COUNT)
                        .map(|col| first.partial_derivative(col).evaluate(coords))
                        .collect()
                })
                .collect(),
        )
    }

    pub fn is_singular_at(&self, point: &ProjectivePoint<T>) -> bool {
        let coords = point.p3_coords();
        self.evaluate(&coords).is_zero()
            && self
                .gradient_at(&coords)
                .into_iter()
                .all(|value| value.is_zero())
    }

    pub fn is_ordinary_double_point_at(&self, point: &ProjectivePoint<T>) -> bool {
        self.is_singular_at(point) && self.hessian_at(&point.p3_coords()).rank() == 3
    }
}

pub fn p3_affine_variable_indices(chart_variable: usize) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
    assert!(
        chart_variable < P3_VARIABLE_COUNT,
        "P3 chart variable index out of range"
    );

    let mut indices = [0; AFFINE_P3_VARIABLE_COUNT];
    let mut affine_index = 0;
    for projective_index in 0..P3_VARIABLE_COUNT {
        if projective_index == chart_variable {
            continue;
        }

        indices[affine_index] = projective_index;
        affine_index += 1;
    }

    indices
}

pub fn dehomogenize_p3_sparse<T: FieldElement>(
    polynomial: &SparsePolynomial<T, P3_VARIABLE_COUNT>,
    chart_variable: usize,
) -> SparsePolynomial<T, AFFINE_P3_VARIABLE_COUNT> {
    assert!(
        chart_variable < P3_VARIABLE_COUNT,
        "P3 chart variable index out of range"
    );

    SparsePolynomial::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let projective_exponents = term.exponents();
                let affine_exponents = std::array::from_fn(|affine_index| {
                    let projective_index = affine_to_projective_index(chart_variable, affine_index);
                    projective_exponents[projective_index]
                });
                (term.coefficient(), affine_exponents)
            })
            .collect(),
    )
}

pub fn affine_hypersurface_singular_generators_p3<T: FieldElement>(
    polynomial: &HomogeneousPolynomialP3<T>,
    chart_variable: usize,
) -> Vec<SparsePolynomial<T, AFFINE_P3_VARIABLE_COUNT>> {
    let affine_polynomial = polynomial.dehomogenize(chart_variable);
    let mut generators = Vec::with_capacity(AFFINE_P3_VARIABLE_COUNT + 1);
    generators.push(affine_polynomial.clone());
    generators.extend(
        (0..AFFINE_P3_VARIABLE_COUNT)
            .map(|variable| affine_polynomial.partial_derivative(variable)),
    );

    generators
}

fn affine_to_projective_index(chart_variable: usize, affine_index: usize) -> usize {
    assert!(
        chart_variable < P3_VARIABLE_COUNT,
        "P3 chart variable index out of range"
    );
    assert!(
        affine_index < AFFINE_P3_VARIABLE_COUNT,
        "affine P3 variable index out of range"
    );

    if affine_index < chart_variable {
        affine_index
    } else {
        affine_index + 1
    }
}

impl<T: FieldElement> From<SparsePolynomial<T, P3_VARIABLE_COUNT>> for HomogeneousPolynomialP3<T> {
    fn from(polynomial: SparsePolynomial<T, P3_VARIABLE_COUNT>) -> Self {
        Self::from_terms(
            polynomial
                .terms()
                .into_iter()
                .map(|term| (term.coefficient(), term.exponents()))
                .collect(),
        )
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MonomialP3<T: FieldElement = Rational> {
    coefficient: T,
    exponents: [usize; P3_VARIABLE_COUNT],
}

impl<T: FieldElement> MonomialP3<T> {
    pub fn coefficient(&self) -> T {
        self.coefficient.clone()
    }

    pub fn exponents(&self) -> [usize; P3_VARIABLE_COUNT] {
        self.exponents
    }

    fn evaluate(&self, coords: &[T; P3_VARIABLE_COUNT]) -> T {
        self.exponents
            .iter()
            .zip(coords)
            .fold(self.coefficient.clone(), |value, (&exponent, coord)| {
                value * coord.pow_usize(exponent)
            })
    }

    fn partial_derivative(&self, variable: usize) -> Option<Self> {
        let exponent = self.exponents[variable];
        if exponent == 0 {
            return None;
        }

        let mut exponents = self.exponents;
        exponents[variable] -= 1;

        Some(Self {
            coefficient: self.coefficient.clone() * repeated_one::<T>(exponent),
            exponents,
        })
    }
}

fn normalize_projective<T: FieldElement>(coords: Vec<T>) -> Vec<T> {
    let first_nonzero = coords
        .iter()
        .position(|coord| !coord.is_zero())
        .expect("projective coordinates contain a nonzero entry");
    let scale = coords[first_nonzero].clone();
    coords
        .into_iter()
        .map(|coord| coord / scale.clone())
        .collect()
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let remainder = a % b;
        a = b;
        b = remainder;
    }
    a.abs()
}

fn monomial_degree(exponents: &[usize; P3_VARIABLE_COUNT]) -> usize {
    exponents.iter().sum()
}

fn compare_lex<const N: usize>(lhs: &[usize; N], rhs: &[usize; N]) -> Ordering {
    lhs.iter()
        .zip(rhs)
        .find_map(|(&left, &right)| (left != right).then(|| left.cmp(&right)))
        .unwrap_or(Ordering::Equal)
}

fn compare_total_degree<const N: usize>(lhs: &[usize; N], rhs: &[usize; N]) -> Ordering {
    monomial_degree_n(lhs).cmp(&monomial_degree_n(rhs))
}

fn compare_grevlex<const N: usize>(lhs: &[usize; N], rhs: &[usize; N]) -> Ordering {
    lhs.iter()
        .zip(rhs)
        .rev()
        .find_map(|(&left, &right)| (left != right).then(|| right.cmp(&left)))
        .unwrap_or(Ordering::Equal)
}

fn monomial_degree_n<const N: usize>(exponents: &[usize; N]) -> usize {
    exponents.iter().sum()
}

fn evaluate_sparse_term<T: FieldElement, const N: usize>(
    coefficient: T,
    exponents: &[usize; N],
    coords: &[T; N],
) -> T {
    exponents
        .iter()
        .zip(coords)
        .fold(coefficient, |value, (&exponent, coord)| {
            value * coord.pow_usize(exponent)
        })
}

fn monomial_quotient<const N: usize>(
    dividend: &[usize; N],
    divisor: &[usize; N],
) -> Option<[usize; N]> {
    let mut quotient = [0; N];
    for index in 0..N {
        if dividend[index] < divisor[index] {
            return None;
        }
        quotient[index] = dividend[index] - divisor[index];
    }

    Some(quotient)
}

fn monomial_divides<const N: usize>(divisor: &[usize; N], dividend: &[usize; N]) -> bool {
    monomial_quotient(dividend, divisor).is_some()
}

fn monomial_lcm<const N: usize>(lhs: &[usize; N], rhs: &[usize; N]) -> [usize; N] {
    std::array::from_fn(|index| lhs[index].max(rhs[index]))
}

fn standard_monomial_bounds<const N: usize>(
    leading_monomials: &[[usize; N]],
) -> Option<[usize; N]> {
    let mut bounds = [usize::MAX; N];

    for leading in leading_monomials {
        let nonzero_variables: Vec<_> = leading
            .iter()
            .enumerate()
            .filter_map(|(index, &exponent)| (exponent > 0).then_some((index, exponent)))
            .collect();
        let [(variable, exponent)] = nonzero_variables.as_slice() else {
            continue;
        };

        bounds[*variable] = bounds[*variable].min(*exponent);
    }

    bounds
        .into_iter()
        .all(|bound| bound != usize::MAX)
        .then_some(bounds)
}

fn enumerate_exponents_below_bounds<const N: usize>(
    bounds: &[usize; N],
    current: &mut [usize; N],
    variable: usize,
    visit: &mut impl FnMut(&[usize; N]),
) {
    if variable == N {
        visit(current);
        return;
    }

    for exponent in 0..bounds[variable] {
        current[variable] = exponent;
        enumerate_exponents_below_bounds(bounds, current, variable + 1, visit);
    }
}

pub fn parse_groebner_lift_certificate<const N: usize, T>(
    input: &str,
) -> Result<GroebnerLiftCertificate<N, T>, String>
where
    T: FieldElement + FromStr,
    <T as FromStr>::Err: fmt::Display,
{
    let lines = input
        .lines()
        .enumerate()
        .filter_map(|(zero_based_line, raw_line)| {
            let without_hash_comment = raw_line
                .split_once('#')
                .map_or(raw_line, |(before_comment, _)| before_comment);
            let without_slash_comment = without_hash_comment
                .split_once("//")
                .map_or(without_hash_comment, |(before_comment, _)| before_comment);
            let line = without_slash_comment.trim();
            (!line.is_empty()).then_some((zero_based_line + 1, line.to_string()))
        })
        .collect::<Vec<_>>();
    let mut cursor = 0;

    let source_count = parse_lift_count(&lines, &mut cursor, "source_count")
        .ok_or_else(|| "lift certificate is missing a source_count declaration".to_string())?;
    let target_count = parse_lift_count(&lines, &mut cursor, "target_count")
        .ok_or_else(|| "lift certificate is missing a target_count declaration".to_string())?;

    let mut coefficients = Vec::with_capacity(target_count);
    for target_index in 0..target_count {
        let (line_number, line) = lines
            .get(cursor)
            .ok_or_else(|| format!("missing target {target_index} declaration"))?;
        let tokens = line.split_whitespace().collect::<Vec<_>>();
        match tokens.as_slice() {
            ["target", value] => {
                let parsed_target = value.parse::<usize>().map_err(|error| {
                    format!("line {line_number}: invalid target index `{value}`: {error}")
                })?;
                if parsed_target != target_index {
                    return Err(format!(
                        "line {line_number}: expected target {target_index}, got {parsed_target}"
                    ));
                }
            }
            _ => {
                return Err(format!(
                    "line {line_number}: expected target {target_index} declaration"
                ));
            }
        }
        cursor += 1;

        let mut target_coefficients = Vec::with_capacity(source_count);
        for _ in 0..source_count {
            target_coefficients.push(parse_lift_polynomial(&lines, &mut cursor)?);
        }
        coefficients.push(target_coefficients);
    }

    if let Some((line_number, line)) = lines.get(cursor) {
        return Err(format!(
            "line {line_number}: unexpected trailing lift certificate line `{line}`"
        ));
    }

    Ok(GroebnerLiftCertificate::new(source_count, coefficients))
}

fn parse_lift_count(lines: &[(usize, String)], cursor: &mut usize, keyword: &str) -> Option<usize> {
    let (line_number, line) = lines.get(*cursor)?;
    let tokens = line.split_whitespace().collect::<Vec<_>>();
    let [found_keyword, value] = tokens.as_slice() else {
        return None;
    };
    if *found_keyword != keyword {
        return None;
    }

    let count = value
        .parse::<usize>()
        .map_err(|error| format!("line {line_number}: invalid {keyword} `{value}`: {error}"))
        .ok()?;
    *cursor += 1;
    Some(count)
}

fn parse_lift_polynomial<const N: usize, T>(
    lines: &[(usize, String)],
    cursor: &mut usize,
) -> Result<SparsePolynomial<T, N>, String>
where
    T: FieldElement + FromStr,
    <T as FromStr>::Err: fmt::Display,
{
    let (line_number, line) = lines
        .get(*cursor)
        .ok_or_else(|| "missing lift polynomial block".to_string())?;
    if !line.eq_ignore_ascii_case("poly") {
        return Err(format!("line {line_number}: expected `poly`"));
    }
    *cursor += 1;

    let mut terms = Vec::new();
    loop {
        let (line_number, line) = lines
            .get(*cursor)
            .ok_or_else(|| "unterminated lift polynomial block".to_string())?;
        *cursor += 1;
        if line.eq_ignore_ascii_case("end") {
            return Ok(SparsePolynomial::from_terms(terms));
        }

        terms.push(parse_lift_term::<N, T>(*line_number, line)?);
    }
}

fn parse_lift_term<const N: usize, T>(
    line_number: usize,
    line: &str,
) -> Result<(T, [usize; N]), String>
where
    T: FieldElement + FromStr,
    <T as FromStr>::Err: fmt::Display,
{
    let tokens = line.split_whitespace().collect::<Vec<_>>();
    if tokens.len() != N + 1 {
        return Err(format!(
            "line {line_number}: expected coefficient plus {N} exponents"
        ));
    }

    let coefficient = tokens[0]
        .parse::<T>()
        .map_err(|error| format!("line {line_number}: invalid coefficient: {error}"))?;
    let mut exponents = [0; N];
    for (index, token) in tokens[1..].iter().enumerate() {
        exponents[index] = token
            .parse::<usize>()
            .map_err(|error| format!("line {line_number}: invalid exponent `{token}`: {error}"))?;
    }

    Ok((coefficient, exponents))
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CertificateSection {
    None,
    Generators,
    Basis,
}

fn parse_groebner_certificate<const N: usize, T>(
    input: &str,
) -> Result<GroebnerCertificate<N, T>, GroebnerCertificateParseError>
where
    T: FieldElement + FromStr,
    <T as FromStr>::Err: fmt::Display,
{
    let mut order = None;
    let mut section = CertificateSection::None;
    let mut current_polynomial = None::<(usize, Vec<(T, [usize; N])>)>;
    let mut generators = Vec::new();
    let mut basis = Vec::new();

    for (zero_based_line, raw_line) in input.lines().enumerate() {
        let line_number = zero_based_line + 1;
        let line = raw_line
            .split_once('#')
            .map_or(raw_line, |(before_comment, _)| before_comment)
            .trim();
        if line.is_empty() {
            continue;
        }

        if current_polynomial.is_some() {
            if line.eq_ignore_ascii_case("end") {
                let (start_line, terms) = current_polynomial
                    .take()
                    .expect("current polynomial exists while parsing end");
                if terms.is_empty() {
                    return Err(parse_error(start_line, "polynomial has no nonzero terms"));
                }
                let polynomial = SparsePolynomial::from_terms(terms);
                match section {
                    CertificateSection::Generators => generators.push(polynomial),
                    CertificateSection::Basis => basis.push(polynomial),
                    CertificateSection::None => {
                        return Err(parse_error(
                            line_number,
                            "`poly` appeared outside a section",
                        ));
                    }
                }
                continue;
            }

            let (_, terms) = current_polynomial
                .as_mut()
                .expect("current polynomial exists while parsing a term");
            terms.push(parse_certificate_term::<N, T>(line_number, line)?);
            continue;
        }

        let tokens: Vec<_> = line.split_whitespace().collect();
        match tokens.as_slice() {
            ["order", value] => {
                if order.is_some() {
                    return Err(parse_error(line_number, "duplicate order declaration"));
                }
                order = Some(
                    value
                        .parse()
                        .map_err(|message| parse_error(line_number, message))?,
                );
            }
            ["generators"] => section = CertificateSection::Generators,
            ["basis"] => section = CertificateSection::Basis,
            ["poly"] => {
                if section == CertificateSection::None {
                    return Err(parse_error(
                        line_number,
                        "`poly` appeared outside a section",
                    ));
                }
                current_polynomial = Some((line_number, Vec::new()));
            }
            ["end"] => return Err(parse_error(line_number, "`end` without matching `poly`")),
            _ => {
                return Err(parse_error(
                    line_number,
                    "expected `order <lex|grlex|grevlex>`, `generators`, `basis`, or `poly`",
                ));
            }
        }
    }

    if let Some((start_line, _)) = current_polynomial {
        return Err(parse_error(start_line, "unterminated polynomial block"));
    }

    let order = order.ok_or_else(|| parse_error(0, "missing order declaration"))?;
    if generators.is_empty() {
        return Err(parse_error(0, "certificate has no generators"));
    }
    if basis.is_empty() {
        return Err(parse_error(0, "certificate has no basis polynomials"));
    }

    Ok(GroebnerCertificate::new(order, generators, basis))
}

fn parse_certificate_term<const N: usize, T>(
    line_number: usize,
    line: &str,
) -> Result<(T, [usize; N]), GroebnerCertificateParseError>
where
    T: FieldElement + FromStr,
    <T as FromStr>::Err: fmt::Display,
{
    let tokens: Vec<_> = line.split_whitespace().collect();
    if tokens.len() != N + 1 {
        return Err(parse_error(
            line_number,
            format!("expected coefficient plus {N} exponents"),
        ));
    }

    let coefficient = tokens[0]
        .parse::<T>()
        .map_err(|message| parse_error(line_number, message.to_string()))?;
    let mut exponents = [0; N];
    for (index, token) in tokens[1..].iter().enumerate() {
        exponents[index] = token.parse::<usize>().map_err(|error| {
            parse_error(
                line_number,
                format!("invalid exponent `{token}` at position {index}: {error}"),
            )
        })?;
    }

    Ok((coefficient, exponents))
}

fn parse_error(line: usize, message: impl Into<String>) -> GroebnerCertificateParseError {
    GroebnerCertificateParseError {
        line,
        message: message.into(),
    }
}

fn repeated_one<T: FieldElement>(count: usize) -> T {
    (0..count).fold(T::zero(), |sum, _| sum + T::one())
}

fn write_quadratic_irrational_part(
    f: &mut fmt::Formatter<'_>,
    coefficient: Rational,
    radicand: i64,
) -> fmt::Result {
    if coefficient == Rational::ONE {
        write!(f, "sqrt({radicand})")
    } else {
        write!(f, "{coefficient}*sqrt({radicand})")
    }
}

#[cfg(test)]
mod tests {
    use super::{
        BigQuadraticRational, BigRational, GroebnerCertificate, HomogeneousPolynomialP3, Matrix,
        MonomialOrder, ProjectivePoint, QuadraticRational, Rational, SparsePolynomial,
        affine_hypersurface_singular_generators_p3, dehomogenize_p3_sparse,
        p3_affine_variable_indices,
    };

    #[test]
    fn rational_normalizes_sign_and_gcd() {
        assert_eq!(Rational::new(2, -4).to_string(), "-1/2");
        assert_eq!(Rational::new(-6, -9).to_string(), "2/3");
        assert_eq!(Rational::new(2, 3).pow_usize(3).to_string(), "8/27");
        assert_eq!("6/9".parse::<Rational>(), Ok(Rational::new(2, 3)));
        assert_eq!("-4".parse::<Rational>(), Ok(Rational::from_i64(-4)));
    }

    #[test]
    fn big_quadratic_rational_parses_singular_sqrt5_coefficients() {
        let coefficient = "(1/2*t-5/2)"
            .parse::<BigQuadraticRational>()
            .expect("coefficient parses");
        let expected = BigQuadraticRational::from(QuadraticRational::new(
            Rational::new(-5, 2),
            Rational::new(1, 2),
            5,
        ));

        assert_eq!(coefficient, expected);

        let sqrt_five = "t".parse::<BigQuadraticRational>().expect("sqrt(5) parses");
        assert_eq!(
            sqrt_five.clone() * sqrt_five,
            BigQuadraticRational::from_i64(5)
        );
    }

    #[test]
    fn matrix_rank_and_nullspace_are_exact() {
        let matrix = Matrix::<Rational>::from_rows(vec![
            vec![1.into(), 0.into(), 0.into(), 0.into()],
            vec![0.into(), 1.into(), 0.into(), 0.into()],
            vec![0.into(), 0.into(), (-1).into(), 0.into()],
            vec![0.into(), 0.into(), 0.into(), 0.into()],
        ]);

        let nullspace = matrix.nullspace();
        assert_eq!(matrix.rank(), 3);
        assert_eq!(
            nullspace,
            vec![vec![0.into(), 0.into(), 0.into(), 1.into()]]
        );
    }

    #[test]
    fn sparse_polynomial_arithmetic_and_derivatives_are_exact() {
        let x = SparsePolynomial::<Rational, 2>::variable(0);
        let y = SparsePolynomial::<Rational, 2>::variable(1);
        let polynomial = x.pow_usize(2).add(&x.mul(&y).scale(3.into())).sub(&y);

        assert_eq!(polynomial.degree(), 2);
        assert!(!polynomial.is_homogeneous());
        assert_eq!(polynomial.evaluate(&[2.into(), 5.into()]), 29.into());
        assert_eq!(
            polynomial
                .partial_derivative(0)
                .evaluate(&[2.into(), 5.into()]),
            19.into()
        );
        assert_eq!(
            polynomial
                .partial_derivative(1)
                .evaluate(&[2.into(), 5.into()]),
            5.into()
        );
    }

    #[test]
    fn sparse_polynomial_normal_form_reduces_by_leading_terms() {
        let x = SparsePolynomial::<Rational, 2>::variable(0);
        let y = SparsePolynomial::<Rational, 2>::variable(1);
        let basis = vec![x.pow_usize(2).sub(&y)];
        let normal_form = x.pow_usize(3).normal_form(&basis, MonomialOrder::Lex);

        assert_eq!(normal_form, x.mul(&y));
        assert_eq!(
            x.pow_usize(2)
                .leading_term(MonomialOrder::GrevLex)
                .expect("nonzero polynomial has a leading term")
                .exponents(),
            [2, 0]
        );
    }

    #[test]
    fn sparse_polynomial_verifies_groebner_basis_by_buchberger_criterion() {
        let x = SparsePolynomial::<Rational, 2>::variable(0);
        let y = SparsePolynomial::<Rational, 2>::variable(1);
        let original_generators = vec![
            x.pow_usize(2).sub(&y),
            x.mul(&y).sub(&SparsePolynomial::constant(1.into())),
        ];
        let groebner_basis = vec![
            x.sub(&y.pow_usize(2)),
            y.pow_usize(3).sub(&SparsePolynomial::constant(1.into())),
        ];

        assert!(!SparsePolynomial::is_groebner_basis(
            &original_generators,
            MonomialOrder::Lex
        ));
        assert!(SparsePolynomial::is_groebner_basis(
            &groebner_basis,
            MonomialOrder::Lex
        ));
        assert!(SparsePolynomial::all_reduce_to_zero(
            &original_generators,
            &groebner_basis,
            MonomialOrder::Lex
        ));
        assert_eq!(
            SparsePolynomial::standard_monomials(&groebner_basis, MonomialOrder::Lex),
            Some(vec![[0, 0], [0, 1], [0, 2]])
        );
        assert_eq!(
            SparsePolynomial::quotient_dimension(&groebner_basis, MonomialOrder::Lex),
            Some(3)
        );

        let s_polynomial = groebner_basis[0]
            .s_polynomial(&groebner_basis[1], MonomialOrder::Lex)
            .expect("nonzero polynomials produce an S-polynomial");
        assert!(
            s_polynomial
                .normal_form(&groebner_basis, MonomialOrder::Lex)
                .is_zero()
        );
    }

    #[test]
    fn sparse_polynomial_standard_monomials_detect_non_zero_dimensional_basis() {
        let x = SparsePolynomial::<Rational, 2>::variable(0);
        let y = SparsePolynomial::<Rational, 2>::variable(1);
        let basis = vec![x.mul(&y)];

        assert_eq!(
            SparsePolynomial::standard_monomials(&basis, MonomialOrder::Lex),
            None
        );
        assert_eq!(
            SparsePolynomial::quotient_dimension(&basis, MonomialOrder::Lex),
            None
        );
    }

    #[test]
    fn sparse_polynomial_standard_monomials_handle_unit_ideal() {
        let basis = vec![SparsePolynomial::<Rational, 2>::constant(1.into())];

        assert_eq!(
            SparsePolynomial::standard_monomials(&basis, MonomialOrder::Lex),
            Some(Vec::new())
        );
        assert_eq!(
            SparsePolynomial::quotient_dimension(&basis, MonomialOrder::Lex),
            Some(0)
        );
    }

    #[test]
    fn groebner_certificate_imports_and_verifies_text_format() {
        let certificate = r#"
            # x^2 - y, xy - 1; lex order with x > y.
            order lex

            generators
            poly
              1 2 0
              -1 0 1
            end
            poly
              1 1 1
              -1 0 0
            end

            basis
            poly
              1 1 0
              -1 0 2
            end
            poly
              1 0 3
              -1 0 0
            end
        "#
        .parse::<GroebnerCertificate<2>>()
        .expect("fixture certificate parses");

        assert_eq!(certificate.order(), MonomialOrder::Lex);
        assert_eq!(certificate.generators().len(), 2);
        assert_eq!(certificate.basis().len(), 2);
        assert_eq!(certificate.quotient_dimension(), Some(3));
        assert_eq!(
            certificate.standard_monomials(),
            Some(vec![[0, 0], [0, 1], [0, 2]])
        );

        let verification = certificate.verify();
        assert!(verification.basis_is_groebner());
        assert!(verification.generators_reduce_to_zero());
        assert!(verification.verified());
    }

    #[test]
    fn groebner_certificate_accepts_big_rational_coefficients() {
        let certificate = r#"
            order lex

            generators
            poly
              12345678901234567890123456789012345678901234567890 1 0
            end
            poly
              -987654321098765432109876543210987654321/7 0 1
            end

            basis
            poly
              1 1 0
            end
            poly
              1 0 1
            end
        "#
        .parse::<GroebnerCertificate<2, BigRational>>()
        .expect("big-rational certificate parses");

        assert_eq!(certificate.quotient_dimension(), Some(1));
        assert_eq!(
            certificate.generators()[0].coefficient(&[1, 0]).to_string(),
            "12345678901234567890123456789012345678901234567890"
        );
        assert_eq!(
            certificate.generators()[1].coefficient(&[0, 1]).to_string(),
            "-987654321098765432109876543210987654321/7"
        );

        let verification = certificate.verify();
        assert!(verification.basis_is_groebner());
        assert!(verification.generators_reduce_to_zero());
        assert!(verification.verified());
    }

    #[test]
    fn groebner_certificate_reports_parse_errors() {
        let error = r#"
            order lex
            generators
            poly
              1 2
            end
        "#
        .parse::<GroebnerCertificate<2>>()
        .expect_err("term with too few exponents is rejected");

        assert_eq!(error.line(), 5);
        assert!(
            error
                .message()
                .contains("expected coefficient plus 2 exponents")
        );
    }

    #[test]
    fn projective_points_normalize_first_nonzero_coordinate() {
        let point = ProjectivePoint::new(vec![0.into(), Rational::new(2, 3), 4.into()]);
        assert_eq!(point.to_string(), "[0:1:6]");
    }

    #[test]
    fn homogeneous_polynomial_evaluates_gradient_and_hessian_exactly() {
        let polynomial = HomogeneousPolynomialP3::<Rational>::from_terms(vec![
            (1.into(), [2, 0, 0, 0]),
            (1.into(), [0, 2, 0, 0]),
            ((-1).into(), [0, 0, 2, 0]),
        ]);
        let point = [3.into(), 4.into(), 5.into(), 1.into()];

        assert_eq!(polynomial.degree(), 2);
        assert_eq!(polynomial.evaluate(&point), 0.into());
        assert_eq!(
            polynomial.gradient_at(&point),
            [6.into(), 8.into(), (-10).into(), 0.into()]
        );
        assert_eq!(polynomial.hessian_at(&point).rank(), 3);
    }

    #[test]
    fn homogeneous_polynomial_combines_terms_and_removes_zero_terms() {
        let polynomial = HomogeneousPolynomialP3::<Rational>::from_terms(vec![
            (1.into(), [1, 0, 0, 0]),
            ((-1).into(), [1, 0, 0, 0]),
        ]);

        assert_eq!(polynomial.degree(), 0);
        assert!(polynomial.terms().is_empty());
    }

    #[test]
    fn p3_dehomogenization_drops_the_chart_variable() {
        let polynomial = SparsePolynomial::<Rational, 4>::from_terms(vec![
            (2.into(), [2, 0, 0, 1]),
            (3.into(), [0, 1, 2, 0]),
        ]);

        assert_eq!(p3_affine_variable_indices(3), [0, 1, 2]);
        assert_eq!(p3_affine_variable_indices(1), [0, 2, 3]);
        assert_eq!(
            dehomogenize_p3_sparse(&polynomial, 3),
            SparsePolynomial::<Rational, 3>::from_terms(vec![
                (2.into(), [2, 0, 0]),
                (3.into(), [0, 1, 2]),
            ])
        );
        assert_eq!(
            dehomogenize_p3_sparse(&polynomial, 1),
            SparsePolynomial::<Rational, 3>::from_terms(vec![
                (2.into(), [2, 0, 1]),
                (3.into(), [0, 2, 0]),
            ])
        );
    }

    #[test]
    fn affine_singular_generators_are_the_chart_equations() {
        let polynomial = HomogeneousPolynomialP3::<Rational>::from_terms(vec![
            (1.into(), [2, 0, 0, 0]),
            (1.into(), [0, 2, 0, 0]),
            (1.into(), [0, 0, 2, 0]),
            ((-1).into(), [0, 0, 0, 2]),
        ]);
        let x = SparsePolynomial::<Rational, 3>::variable(0);
        let y = SparsePolynomial::<Rational, 3>::variable(1);
        let z = SparsePolynomial::<Rational, 3>::variable(2);

        let generators = affine_hypersurface_singular_generators_p3(&polynomial, 3);

        assert_eq!(generators.len(), 4);
        assert_eq!(
            generators[0],
            x.pow_usize(2)
                .add(&y.pow_usize(2))
                .add(&z.pow_usize(2))
                .sub(&SparsePolynomial::constant(1.into()))
        );
        assert_eq!(generators[1], x.scale(2.into()));
        assert_eq!(generators[2], y.scale(2.into()));
        assert_eq!(generators[3], z.scale(2.into()));
        assert_eq!(polynomial.affine_singular_generators(3), generators);
    }

    #[test]
    fn quadratic_rational_arithmetic_is_exact() {
        let sqrt_two = QuadraticRational::sqrt(2);
        let half = Rational::new(1, 2);
        let half_sqrt_two = QuadraticRational::new(Rational::ZERO, half, 2);

        assert_eq!(sqrt_two * sqrt_two, QuadraticRational::from_i64(2));
        assert_eq!(
            half_sqrt_two * half_sqrt_two,
            QuadraticRational::from_rational(half)
        );
        assert_eq!(
            (QuadraticRational::from_i64(1) + sqrt_two)
                / (QuadraticRational::from_i64(1) - sqrt_two),
            QuadraticRational::new((-3).into(), (-2).into(), 2)
        );
    }

    #[test]
    fn quadratic_rational_parses_singular_sqrt5_coefficients() {
        assert_eq!(
            "(1/20t-1/4)".parse::<QuadraticRational>(),
            Ok(QuadraticRational::new(
                Rational::new(-1, 4),
                Rational::new(1, 20),
                5
            ))
        );
        assert_eq!(
            "(-t-1)".parse::<QuadraticRational>(),
            Ok(QuadraticRational::new((-1).into(), (-1).into(), 5))
        );
        assert_eq!(
            "7/3".parse::<QuadraticRational>(),
            Ok(QuadraticRational::from_rational(Rational::new(7, 3)))
        );
    }
}
