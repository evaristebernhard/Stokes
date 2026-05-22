use nodal_core::{
    AFFINE_P3_VARIABLE_COUNT, BigQuadraticRational, GroebnerCertificate,
    GroebnerCertificateParseError, GroebnerLiftCertificate, HomogeneousPolynomialP3, Matrix,
    MonomialOrder, P3_VARIABLE_COUNT, ProjectivePoint, ProjectiveSupport, QuadraticRational,
    SparsePolynomial, p3_affine_variable_indices, parse_groebner_lift_certificate,
};
use std::collections::BTreeMap;

pub const BARTH_NODE_COUNT: usize = 65;
pub const BARTH_NODE_A_COUNT: usize = 15;
pub const BARTH_NODE_B_COUNT: usize = 30;
pub const BARTH_NODE_C_COUNT: usize = 20;
pub const BARTH_MID_LINE_COUNT: usize = 15;
pub const BARTH_CENTRE_LINE_COUNT: usize = 10;
pub const BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT: usize = (1 << P3_VARIABLE_COUNT) - 1;
pub const BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT: usize = AFFINE_P3_VARIABLE_COUNT + 1;

type Q5 = QuadraticRational;
type PolynomialP3 = SparsePolynomial<Q5, P3_VARIABLE_COUNT>;
type PolynomialA3 = SparsePolynomial<Q5, AFFINE_P3_VARIABLE_COUNT>;
type PolynomialA4 = SparsePolynomial<Q5, BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
type BigPolynomialA4 =
    SparsePolynomial<BigQuadraticRational, BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>;
pub type BarthProjectiveSupport = ProjectiveSupport<P3_VARIABLE_COUNT>;
pub type BarthGroebnerLiftCertificate<const N: usize> =
    GroebnerLiftCertificate<N, BigQuadraticRational>;

const BARTH_PROJECTIVE_SUPPORT_GREVLEX_CERTIFICATES: [&str;
    BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [
    include_str!("../certificates/barth-support-01-grevlex.cert"),
    include_str!("../certificates/barth-support-02-grevlex.cert"),
    include_str!("../certificates/barth-support-03-grevlex.cert"),
    include_str!("../certificates/barth-support-04-grevlex.cert"),
    include_str!("../certificates/barth-support-05-grevlex.cert"),
    include_str!("../certificates/barth-support-06-grevlex.cert"),
    include_str!("../certificates/barth-support-07-grevlex.cert"),
    include_str!("../certificates/barth-support-08-grevlex.cert"),
    include_str!("../certificates/barth-support-09-grevlex.cert"),
    include_str!("../certificates/barth-support-10-grevlex.cert"),
    include_str!("../certificates/barth-support-11-grevlex.cert"),
    include_str!("../certificates/barth-support-12-grevlex.cert"),
    include_str!("../certificates/barth-support-13-grevlex.cert"),
    include_str!("../certificates/barth-support-14-grevlex.cert"),
    include_str!("../certificates/barth-support-15-grevlex.cert"),
];

const BARTH_PROJECTIVE_SUPPORT_GREVLEX_LIFT_CERTIFICATES: [&str;
    BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [
    include_str!("../certificates/barth-support-01-grevlex.lift"),
    include_str!("../certificates/barth-support-02-grevlex.lift"),
    include_str!("../certificates/barth-support-03-grevlex.lift"),
    include_str!("../certificates/barth-support-04-grevlex.lift"),
    include_str!("../certificates/barth-support-05-grevlex.lift"),
    include_str!("../certificates/barth-support-06-grevlex.lift"),
    include_str!("../certificates/barth-support-07-grevlex.lift"),
    include_str!("../certificates/barth-support-08-grevlex.lift"),
    include_str!("../certificates/barth-support-09-grevlex.lift"),
    include_str!("../certificates/barth-support-10-grevlex.lift"),
    include_str!("../certificates/barth-support-11-grevlex.lift"),
    include_str!("../certificates/barth-support-12-grevlex.lift"),
    include_str!("../certificates/barth-support-13-grevlex.lift"),
    include_str!("../certificates/barth-support-14-grevlex.lift"),
    include_str!("../certificates/barth-support-15-grevlex.lift"),
];

pub const BARTH_PROJECTIVE_SUPPORT_STRATUM_LENGTHS: [usize;
    BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT] = [0, 1, 2, 1, 2, 0, 4, 1, 2, 0, 4, 0, 4, 12, 32];

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SexticSurface {
    polynomial: HomogeneousPolynomialP3<Q5>,
}

impl SexticSurface {
    pub fn new(polynomial: HomogeneousPolynomialP3<Q5>) -> Self {
        assert_eq!(polynomial.degree(), 6, "expected a sextic surface");
        Self { polynomial }
    }

    pub fn polynomial(&self) -> &HomogeneousPolynomialP3<Q5> {
        &self.polynomial
    }

    pub fn verify_node(&self, point: ProjectivePoint<Q5>) -> NodeVerification {
        let coords = point.p3_coords();
        let value = self.polynomial.evaluate(&coords);
        let gradient = self.polynomial.gradient_at(&coords);
        let hessian = self.polynomial.hessian_at(&coords);
        let hessian_rank = hessian.rank();

        NodeVerification {
            point,
            value,
            gradient,
            hessian_rank,
            ordinary_double_point: value.is_zero()
                && gradient.iter().all(|value| value.is_zero())
                && hessian_rank == 3,
            hessian,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeVerification {
    point: ProjectivePoint<Q5>,
    value: Q5,
    gradient: [Q5; P3_VARIABLE_COUNT],
    hessian_rank: usize,
    ordinary_double_point: bool,
    hessian: Matrix<Q5>,
}

impl NodeVerification {
    pub fn point(&self) -> &ProjectivePoint<Q5> {
        &self.point
    }

    pub fn value(&self) -> Q5 {
        self.value
    }

    pub fn gradient(&self) -> [Q5; P3_VARIABLE_COUNT] {
        self.gradient
    }

    pub fn hessian_rank(&self) -> usize {
        self.hessian_rank
    }

    pub fn ordinary_double_point(&self) -> bool {
        self.ordinary_double_point
    }

    pub fn hessian(&self) -> &Matrix<Q5> {
        &self.hessian
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BarthNodeClass {
    A,
    B,
    C,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BarthA5Generator {
    Sigma,
    Tau,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum BarthLine {
    Mid(&'static str),
    Centre(&'static str),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BarthNode {
    label: &'static str,
    class: BarthNodeClass,
    line: BarthLine,
    point: ProjectivePoint<Q5>,
}

impl BarthNode {
    pub fn label(&self) -> &'static str {
        self.label
    }

    pub fn class(&self) -> BarthNodeClass {
        self.class
    }

    pub fn line(&self) -> BarthLine {
        self.line
    }

    pub fn point(&self) -> &ProjectivePoint<Q5> {
        &self.point
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BarthProjectiveSupportStratumGenerators {
    support: BarthProjectiveSupport,
    affine_projective_indices: [usize; AFFINE_P3_VARIABLE_COUNT],
    generators: Vec<PolynomialA4>,
}

impl BarthProjectiveSupportStratumGenerators {
    pub fn support(&self) -> &BarthProjectiveSupport {
        &self.support
    }

    pub fn chart_variable(&self) -> usize {
        self.support.chart_variable()
    }

    pub fn affine_projective_indices(&self) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
        self.affine_projective_indices
    }

    pub fn generators(&self) -> &[PolynomialA4] {
        &self.generators
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BarthProjectiveSupportGroebnerCertificate {
    support: BarthProjectiveSupport,
    certificate: GroebnerCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigQuadraticRational>,
}

impl BarthProjectiveSupportGroebnerCertificate {
    pub fn support(&self) -> &BarthProjectiveSupport {
        &self.support
    }

    pub fn certificate(
        &self,
    ) -> &GroebnerCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigQuadraticRational> {
        &self.certificate
    }

    pub fn expected_generators(&self) -> Vec<BigPolynomialA4> {
        barth_projective_support_stratum_generators(self.support.mask())
            .generators
            .into_iter()
            .map(quadratic_polynomial_to_big_quadratic)
            .collect()
    }

    pub fn expected_quotient_length(&self) -> usize {
        BARTH_PROJECTIVE_SUPPORT_STRATUM_LENGTHS[usize::from(self.support.mask() - 1)]
    }

    pub fn generators_match_model(&self) -> bool {
        self.certificate.generators() == self.expected_generators().as_slice()
    }

    pub fn verify(&self) -> BarthProjectiveSupportGroebnerVerification {
        let groebner_verification = self.certificate.verify();
        BarthProjectiveSupportGroebnerVerification {
            support_mask: self.support.mask(),
            order: self.certificate.order(),
            generators_match_model: self.generators_match_model(),
            basis_is_groebner: groebner_verification.basis_is_groebner(),
            generators_reduce_to_zero: groebner_verification.generators_reduce_to_zero(),
            basis_size: self.certificate.basis().len(),
            quotient_dimension: self.certificate.quotient_dimension(),
            expected_quotient_length: self.expected_quotient_length(),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct BarthProjectiveSupportGroebnerVerification {
    support_mask: u8,
    order: MonomialOrder,
    generators_match_model: bool,
    basis_is_groebner: bool,
    generators_reduce_to_zero: bool,
    basis_size: usize,
    quotient_dimension: Option<usize>,
    expected_quotient_length: usize,
}

impl BarthProjectiveSupportGroebnerVerification {
    pub fn support_mask(self) -> u8 {
        self.support_mask
    }

    pub fn order(self) -> MonomialOrder {
        self.order
    }

    pub fn generators_match_model(self) -> bool {
        self.generators_match_model
    }

    pub fn basis_is_groebner(self) -> bool {
        self.basis_is_groebner
    }

    pub fn generators_reduce_to_zero(self) -> bool {
        self.generators_reduce_to_zero
    }

    pub fn basis_size(self) -> usize {
        self.basis_size
    }

    pub fn quotient_dimension(self) -> Option<usize> {
        self.quotient_dimension
    }

    pub fn expected_quotient_length(self) -> usize {
        self.expected_quotient_length
    }

    pub fn verified(self) -> bool {
        self.generators_match_model
            && self.basis_is_groebner
            && self.generators_reduce_to_zero
            && self.quotient_dimension == Some(self.expected_quotient_length)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BarthSingularSchemeCertificate {
    support_strata: Vec<BarthProjectiveSupportGroebnerCertificate>,
    support_lifts: Vec<BarthGroebnerLiftCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>>,
}

impl BarthSingularSchemeCertificate {
    pub fn support_strata(&self) -> &[BarthProjectiveSupportGroebnerCertificate] {
        &self.support_strata
    }

    pub fn support_lifts(
        &self,
    ) -> &[BarthGroebnerLiftCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>] {
        &self.support_lifts
    }

    pub fn verified_projective_length(&self) -> Option<usize> {
        if self.support_strata.len() != self.support_lifts.len() {
            return None;
        }

        let mut length = 0;
        for (stratum, lift) in self.support_strata.iter().zip(&self.support_lifts) {
            let verification = stratum.verify();
            if !verification.verified() {
                return None;
            }
            if !lift.verifies_targets(
                stratum.certificate.generators(),
                stratum.certificate.basis(),
            ) {
                return None;
            }
            length += verification.quotient_dimension()?;
        }
        Some(length)
    }

    pub fn verified_reduced_ordinary_node_count(&self) -> Option<usize> {
        let projective_length = self.verified_projective_length()?;
        let surface = barth_sextic();
        let nodes = barth_nodes();
        if projective_unique_count(&nodes) == projective_length
            && nodes
                .into_iter()
                .all(|node| surface.verify_node(node).ordinary_double_point())
        {
            Some(projective_length)
        } else {
            None
        }
    }
}

pub fn barth_sextic() -> SexticSurface {
    SexticSurface::new(barth_sextic_polynomial())
}

/// Catanese/Barth's sextic in coordinates `[w:x:y:z]`, with denominator cleared.
pub fn barth_sextic_polynomial() -> HomogeneousPolynomialP3<Q5> {
    let w = PolynomialP3::variable(0);
    let x = PolynomialP3::variable(1);
    let y = PolynomialP3::variable(2);
    let z = PolynomialP3::variable(3);

    let tau = tau();
    let tau_squared = tau * tau;
    let first = x.pow_usize(2).scale(tau_squared).sub(&y.pow_usize(2));
    let second = y.pow_usize(2).scale(tau_squared).sub(&z.pow_usize(2));
    let third = z.pow_usize(2).scale(tau_squared).sub(&x.pow_usize(2));
    let sphere = x
        .pow_usize(2)
        .add(&y.pow_usize(2))
        .add(&z.pow_usize(2))
        .sub(&w.pow_usize(2));
    let scale = q(2) * tau + q(1);

    HomogeneousPolynomialP3::from(
        first
            .mul(&second)
            .mul(&third)
            .scale(q(4))
            .sub(&w.pow_usize(2).mul(&sphere.pow_usize(2)).scale(scale)),
    )
}

pub fn barth_affine_chart_generators(chart_variable: usize) -> Vec<PolynomialA3> {
    barth_sextic_polynomial().affine_singular_generators(chart_variable)
}

pub fn barth_affine_chart_variable_indices(
    chart_variable: usize,
) -> [usize; AFFINE_P3_VARIABLE_COUNT] {
    p3_affine_variable_indices(chart_variable)
}

pub fn barth_projective_support_stratum_generators(
    support_mask: u8,
) -> BarthProjectiveSupportStratumGenerators {
    let support = BarthProjectiveSupport::new(support_mask);
    let chart_generators = barth_affine_chart_generators(support.chart_variable());
    let affine_projective_indices = barth_affine_chart_variable_indices(support.chart_variable());
    let mut generators = chart_generators
        .into_iter()
        .map(lift_affine3_polynomial_to_stratum)
        .collect::<Vec<_>>();

    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if !support.contains_projective_variable(projective_variable) {
            generators.push(PolynomialA4::variable(affine_variable));
        }
    }

    let mut nonzero_product_exponents = [0; BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT];
    for (affine_variable, &projective_variable) in affine_projective_indices.iter().enumerate() {
        if support.contains_projective_variable(projective_variable) {
            nonzero_product_exponents[affine_variable] = 1;
        }
    }
    nonzero_product_exponents[AFFINE_P3_VARIABLE_COUNT] = 1;
    generators.push(PolynomialA4::from_terms(vec![
        (Q5::ONE, nonzero_product_exponents),
        (-Q5::ONE, [0; BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT]),
    ]));

    BarthProjectiveSupportStratumGenerators {
        support,
        affine_projective_indices,
        generators,
    }
}

pub fn barth_projective_support_grevlex_certificate(
    support_mask: u8,
) -> Result<BarthProjectiveSupportGroebnerCertificate, GroebnerCertificateParseError> {
    let support = BarthProjectiveSupport::new(support_mask);
    let certificate = BARTH_PROJECTIVE_SUPPORT_GREVLEX_CERTIFICATES
        [usize::from(support_mask - 1)]
    .parse::<GroebnerCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT, BigQuadraticRational>>()?;

    Ok(BarthProjectiveSupportGroebnerCertificate {
        support,
        certificate,
    })
}

pub fn barth_projective_support_grevlex_certificates()
-> Result<Vec<BarthProjectiveSupportGroebnerCertificate>, GroebnerCertificateParseError> {
    (1..=BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| barth_projective_support_grevlex_certificate(support_mask as u8))
        .collect()
}

pub fn barth_projective_support_grevlex_lift_certificate(
    support_mask: u8,
) -> Result<BarthGroebnerLiftCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>, String> {
    let index = usize::from(support_mask)
        .checked_sub(1)
        .filter(|&index| index < BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .ok_or_else(|| format!("support mask {support_mask} is out of range"))?;

    parse_groebner_lift_certificate(BARTH_PROJECTIVE_SUPPORT_GREVLEX_LIFT_CERTIFICATES[index])
}

pub fn barth_projective_support_grevlex_lift_certificates()
-> Result<Vec<BarthGroebnerLiftCertificate<BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>>, String> {
    (1..=BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT)
        .map(|support_mask| barth_projective_support_grevlex_lift_certificate(support_mask as u8))
        .collect()
}

pub fn barth_singular_scheme_certificate() -> Result<BarthSingularSchemeCertificate, String> {
    Ok(BarthSingularSchemeCertificate {
        support_strata: barth_projective_support_grevlex_certificates()
            .map_err(|error| error.to_string())?,
        support_lifts: barth_projective_support_grevlex_lift_certificates()?,
    })
}

pub fn barth_node_records() -> Vec<BarthNode> {
    let mut nodes = Vec::with_capacity(BARTH_NODE_COUNT);

    nodes.extend([
        node_a("A(12)(34)", "12|34", [q(0), q(1), tau(), -tau_bar()]),
        node_a("A(41)(25)", "14|25", [q(0), q(-1), tau(), -tau_bar()]),
        node_a("A(31)(52)", "13|25", [q(0), q(1), -tau(), -tau_bar()]),
        node_a("A(51)(34)", "15|34", [q(0), q(1), tau(), tau_bar()]),
        node_a("A(12)(53)", "12|35", [q(0), -tau_bar(), q(1), tau()]),
        node_a("A(41)(53)", "14|35", [q(0), tau_bar(), q(1), tau()]),
        node_a("A(31)(24)", "13|24", [q(0), -tau_bar(), q(-1), tau()]),
        node_a("A(51)(42)", "15|24", [q(0), -tau_bar(), q(1), -tau()]),
        node_a("A(12)(45)", "12|45", [q(0), tau(), -tau_bar(), q(1)]),
        node_a("A(41)(32)", "14|23", [q(0), -tau(), -tau_bar(), q(1)]),
        node_a("A(31)(45)", "13|45", [q(0), tau(), tau_bar(), q(1)]),
        node_a("A(51)(23)", "15|23", [q(0), tau(), -tau_bar(), q(-1)]),
        node_a("A(23)(45)", "23|45", [q(0), q(1), q(0), q(0)]),
        node_a("A(25)(34)", "25|34", [q(0), q(0), q(1), q(0)]),
        node_a("A(24)(53)", "24|35", [q(0), q(0), q(0), q(1)]),
    ]);

    nodes.extend([
        node_b("B12(34)", "12|34", [q(2), q(1), tau(), -tau_bar()]),
        node_b("B41(25)", "14|25", [q(2), q(-1), tau(), -tau_bar()]),
        node_b("B31(52)", "13|25", [q(2), q(1), -tau(), -tau_bar()]),
        node_b("B51(34)", "15|34", [q(2), q(1), tau(), tau_bar()]),
        node_b("B21(43)", "12|34", [q(2), q(-1), -tau(), tau_bar()]),
        node_b("B14(52)", "14|25", [q(2), q(1), -tau(), tau_bar()]),
        node_b("B13(25)", "13|25", [q(2), q(-1), tau(), tau_bar()]),
        node_b("B15(43)", "15|34", [q(2), q(-1), -tau(), -tau_bar()]),
        node_b("B12(53)", "12|35", [q(2), -tau_bar(), q(1), tau()]),
        node_b("B41(53)", "14|35", [q(2), tau_bar(), q(1), tau()]),
        node_b("B31(24)", "13|24", [q(2), -tau_bar(), q(-1), tau()]),
        node_b("B51(42)", "15|24", [q(2), -tau_bar(), q(1), -tau()]),
        node_b("B21(35)", "12|35", [q(2), tau_bar(), q(-1), -tau()]),
        node_b("B14(35)", "14|35", [q(2), -tau_bar(), q(-1), -tau()]),
        node_b("B13(42)", "13|24", [q(2), tau_bar(), q(1), -tau()]),
        node_b("B15(24)", "15|24", [q(2), tau_bar(), q(-1), tau()]),
        node_b("B12(45)", "12|45", [q(2), tau(), -tau_bar(), q(1)]),
        node_b("B41(32)", "14|23", [q(2), -tau(), -tau_bar(), q(1)]),
        node_b("B31(45)", "13|45", [q(2), tau(), tau_bar(), q(1)]),
        node_b("B51(23)", "15|23", [q(2), tau(), -tau_bar(), q(-1)]),
        node_b("B21(54)", "12|45", [q(2), -tau(), tau_bar(), q(-1)]),
        node_b("B14(23)", "14|23", [q(2), tau(), tau_bar(), q(-1)]),
        node_b("B13(54)", "13|45", [q(2), -tau(), -tau_bar(), q(-1)]),
        node_b("B15(32)", "15|23", [q(2), -tau(), tau_bar(), q(1)]),
        node_b("B23(45)", "23|45", [q(1), q(1), q(0), q(0)]),
        node_b("B32(54)", "23|45", [q(1), q(-1), q(0), q(0)]),
        node_b("B25(34)", "25|34", [q(1), q(0), q(1), q(0)]),
        node_b("B52(43)", "25|34", [q(1), q(0), q(-1), q(0)]),
        node_b("B24(53)", "24|35", [q(1), q(0), q(0), q(1)]),
        node_b("B42(35)", "24|35", [q(1), q(0), q(0), q(-1)]),
    ]);

    nodes.extend([
        node_c("C12", "12", [q(1), q(1), q(1), q(1)]),
        node_c("C41", "14", [q(1), q(-1), q(1), q(1)]),
        node_c("C31", "13", [q(1), q(1), q(-1), q(1)]),
        node_c("C51", "15", [q(1), q(1), q(1), q(-1)]),
        node_c("C21", "12", [q(1), q(-1), q(-1), q(-1)]),
        node_c("C14", "14", [q(1), q(1), q(-1), q(-1)]),
        node_c("C13", "13", [q(1), q(-1), q(1), q(-1)]),
        node_c("C15", "15", [q(1), q(-1), q(-1), q(1)]),
        node_c("C53", "35", [q(1), q(0), -tau_bar(), tau()]),
        node_c("C24", "24", [q(1), q(0), tau_bar(), tau()]),
        node_c("C35", "35", [q(1), q(0), tau_bar(), -tau()]),
        node_c("C42", "24", [q(1), q(0), -tau_bar(), -tau()]),
        node_c("C45", "45", [q(1), tau(), q(0), -tau_bar()]),
        node_c("C32", "23", [q(1), -tau(), q(0), -tau_bar()]),
        node_c("C54", "45", [q(1), -tau(), q(0), tau_bar()]),
        node_c("C23", "23", [q(1), tau(), q(0), tau_bar()]),
        node_c("C34", "34", [q(1), -tau_bar(), tau(), q(0)]),
        node_c("C25", "25", [q(1), tau_bar(), tau(), q(0)]),
        node_c("C43", "34", [q(1), tau_bar(), -tau(), q(0)]),
        node_c("C52", "25", [q(1), -tau_bar(), -tau(), q(0)]),
    ]);

    nodes
}

pub fn barth_nodes_a() -> Vec<ProjectivePoint<Q5>> {
    nodes_of_class(BarthNodeClass::A)
}

pub fn barth_nodes_b() -> Vec<ProjectivePoint<Q5>> {
    nodes_of_class(BarthNodeClass::B)
}

pub fn barth_nodes_c() -> Vec<ProjectivePoint<Q5>> {
    nodes_of_class(BarthNodeClass::C)
}

pub fn barth_nodes() -> Vec<ProjectivePoint<Q5>> {
    barth_node_records()
        .into_iter()
        .map(|node| node.point)
        .collect()
}

pub fn barth_nodes_a_orbit() -> Vec<ProjectivePoint<Q5>> {
    orbit_nodes_of_class(BarthNodeClass::A)
}

pub fn barth_nodes_b_orbit() -> Vec<ProjectivePoint<Q5>> {
    orbit_nodes_of_class(BarthNodeClass::B)
}

pub fn barth_nodes_c_orbit() -> Vec<ProjectivePoint<Q5>> {
    orbit_nodes_of_class(BarthNodeClass::C)
}

pub fn barth_a5_orbit_indices(class: BarthNodeClass) -> Vec<usize> {
    let generator_images = [
        barth_a5_node_permutation(class, BarthA5Generator::Sigma),
        barth_a5_node_permutation(class, BarthA5Generator::Tau),
    ];
    generate_orbit_indices(0, &generator_images)
}

pub fn barth_a5_node_permutation(class: BarthNodeClass, generator: BarthA5Generator) -> Vec<usize> {
    match class {
        BarthNodeClass::A => Vec::from(barth_a5_node_permutation_a(generator)),
        BarthNodeClass::B => Vec::from(barth_a5_node_permutation_b(generator)),
        BarthNodeClass::C => Vec::from(barth_a5_node_permutation_c(generator)),
    }
}

pub fn barth_line_label(line: BarthLine) -> &'static str {
    match line {
        BarthLine::Mid(label) | BarthLine::Centre(label) => label,
    }
}

pub fn barth_line_label_after_generator(line: BarthLine, generator: BarthA5Generator) -> String {
    match line {
        BarthLine::Mid(label) => {
            let (lhs, rhs) = label
                .split_once('|')
                .expect("mid line labels are two pairs separated by `|`");
            canonical_mid_label(
                apply_digit_pair(lhs, generator),
                apply_digit_pair(rhs, generator),
            )
        }
        BarthLine::Centre(label) => canonical_pair_label(apply_digit_pair(label, generator)),
    }
}

pub fn barth_mid_line_node_groups() -> BTreeMap<&'static str, Vec<ProjectivePoint<Q5>>> {
    let mut groups = BTreeMap::new();
    for node in barth_node_records() {
        if let BarthLine::Mid(line) = node.line {
            groups.entry(line).or_insert_with(Vec::new).push(node.point);
        }
    }
    groups
}

pub fn barth_centre_line_node_groups() -> BTreeMap<&'static str, Vec<ProjectivePoint<Q5>>> {
    let mut groups = BTreeMap::new();
    for node in barth_node_records() {
        if let BarthLine::Centre(line) = node.line {
            groups.entry(line).or_insert_with(Vec::new).push(node.point);
        }
    }
    groups
}

pub fn points_span_rank(points: &[ProjectivePoint<Q5>]) -> usize {
    Matrix::from_rows(
        points
            .iter()
            .map(|point| point.coords().to_vec())
            .collect::<Vec<_>>(),
    )
    .rank()
}

pub fn projective_unique_count(points: &[ProjectivePoint<Q5>]) -> usize {
    let mut unique = Vec::<ProjectivePoint<Q5>>::new();
    for point in points {
        if !unique.iter().any(|seen| seen == point) {
            unique.push(point.clone());
        }
    }
    unique.len()
}

fn nodes_of_class(class: BarthNodeClass) -> Vec<ProjectivePoint<Q5>> {
    barth_node_records()
        .into_iter()
        .filter(|node| node.class == class)
        .map(|node| node.point)
        .collect()
}

fn orbit_nodes_of_class(class: BarthNodeClass) -> Vec<ProjectivePoint<Q5>> {
    let class_records = records_of_class(class);
    barth_a5_orbit_indices(class)
        .into_iter()
        .map(|index| class_records[index].point.clone())
        .collect()
}

fn records_of_class(class: BarthNodeClass) -> Vec<BarthNode> {
    barth_node_records()
        .into_iter()
        .filter(|node| node.class == class)
        .collect()
}

fn generate_orbit_indices(start: usize, generator_images: &[Vec<usize>; 2]) -> Vec<usize> {
    let mut orbit = Vec::new();
    let mut frontier = vec![start];

    while let Some(index) = frontier.pop() {
        if orbit.contains(&index) {
            continue;
        }
        orbit.push(index);
        for image in generator_images {
            let next = image[index];
            if !orbit.contains(&next) && !frontier.contains(&next) {
                frontier.push(next);
            }
        }
    }

    orbit.sort_unstable();
    orbit
}

fn barth_a5_node_permutation_a(generator: BarthA5Generator) -> [usize; BARTH_NODE_A_COUNT] {
    match generator {
        BarthA5Generator::Sigma => permutation_from_one_based_cycles(&[
            &[1, 10, 7],
            &[2, 15, 4],
            &[3, 5, 12],
            &[6, 8, 14],
            &[9, 13, 11],
        ]),
        BarthA5Generator::Tau => permutation_from_one_based_cycles(&[
            &[1, 11],
            &[3, 14],
            &[4, 7],
            &[5, 13],
            &[6, 10],
            &[12, 15],
        ]),
    }
}

fn barth_a5_node_permutation_b(generator: BarthA5Generator) -> [usize; BARTH_NODE_B_COUNT] {
    match generator {
        BarthA5Generator::Sigma => permutation_from_one_based_cycles(&[
            &[1, 22, 11],
            &[2, 30, 8],
            &[3, 9, 20],
            &[4, 6, 29],
            &[5, 18, 15],
            &[7, 13, 24],
            &[10, 12, 28],
            &[14, 16, 27],
            &[17, 25, 19],
            &[21, 26, 23],
        ]),
        BarthA5Generator::Tau => permutation_from_one_based_cycles(&[
            &[1, 19],
            &[2, 6],
            &[3, 27],
            &[4, 11],
            &[5, 23],
            &[7, 28],
            &[8, 15],
            &[9, 25],
            &[10, 22],
            &[12, 16],
            &[13, 26],
            &[14, 18],
            &[20, 29],
            &[24, 30],
        ]),
    }
}

fn barth_a5_node_permutation_c(generator: BarthA5Generator) -> [usize; BARTH_NODE_C_COUNT] {
    match generator {
        BarthA5Generator::Sigma => permutation_from_one_based_cycles(&[
            &[1, 16, 3],
            &[2, 12, 19],
            &[4, 20, 9],
            &[5, 14, 7],
            &[6, 10, 17],
            &[8, 18, 11],
        ]),
        BarthA5Generator::Tau => permutation_from_one_based_cycles(&[
            &[1, 13],
            &[2, 6],
            &[3, 17],
            &[4, 10],
            &[5, 15],
            &[7, 19],
            &[8, 12],
            &[9, 16],
            &[11, 14],
            &[18, 20],
        ]),
    }
}

fn permutation_from_one_based_cycles<const N: usize>(cycles: &[&[usize]]) -> [usize; N] {
    let mut image = std::array::from_fn(|index| index);
    for cycle in cycles {
        for index in 0..cycle.len() {
            let source = cycle[index]
                .checked_sub(1)
                .expect("cycle entries are one-based");
            let target = cycle[(index + 1) % cycle.len()]
                .checked_sub(1)
                .expect("cycle entries are one-based");
            assert!(source < N && target < N, "cycle entry out of range");
            image[source] = target;
        }
    }
    image
}

fn apply_digit_pair(label: &str, generator: BarthA5Generator) -> [u8; 2] {
    let digits = label
        .chars()
        .map(|digit| apply_a5_digit(parse_a5_digit(digit), generator))
        .collect::<Vec<_>>();
    let [first, second] = digits.as_slice() else {
        panic!("Barth line pair labels must have two digits");
    };
    [*first, *second]
}

fn apply_a5_digit(digit: u8, generator: BarthA5Generator) -> u8 {
    match generator {
        BarthA5Generator::Sigma => match digit {
            1 => 2,
            2 => 3,
            3 => 1,
            _ => digit,
        },
        BarthA5Generator::Tau => match digit {
            1 => 4,
            4 => 1,
            2 => 5,
            5 => 2,
            _ => digit,
        },
    }
}

fn parse_a5_digit(digit: char) -> u8 {
    let value = digit
        .to_digit(10)
        .unwrap_or_else(|| panic!("invalid A5 digit `{digit}`")) as u8;
    assert!((1..=5).contains(&value), "A5 digit out of range");
    value
}

fn canonical_mid_label(lhs: [u8; 2], rhs: [u8; 2]) -> String {
    let mut pairs = [canonical_pair_label(lhs), canonical_pair_label(rhs)];
    pairs.sort();
    format!("{}|{}", pairs[0], pairs[1])
}

fn canonical_pair_label(pair: [u8; 2]) -> String {
    let mut pair = pair;
    pair.sort();
    format!("{}{}", pair[0], pair[1])
}

fn node_a(label: &'static str, line: &'static str, coords: [Q5; P3_VARIABLE_COUNT]) -> BarthNode {
    node(label, BarthNodeClass::A, BarthLine::Mid(line), coords)
}

fn node_b(label: &'static str, line: &'static str, coords: [Q5; P3_VARIABLE_COUNT]) -> BarthNode {
    node(label, BarthNodeClass::B, BarthLine::Mid(line), coords)
}

fn node_c(label: &'static str, line: &'static str, coords: [Q5; P3_VARIABLE_COUNT]) -> BarthNode {
    node(label, BarthNodeClass::C, BarthLine::Centre(line), coords)
}

fn node(
    label: &'static str,
    class: BarthNodeClass,
    line: BarthLine,
    coords: [Q5; P3_VARIABLE_COUNT],
) -> BarthNode {
    BarthNode {
        label,
        class,
        line,
        point: ProjectivePoint::new(coords.to_vec()),
    }
}

fn lift_affine3_polynomial_to_stratum(polynomial: PolynomialA3) -> PolynomialA4 {
    PolynomialA4::from_terms(
        polynomial
            .terms()
            .into_iter()
            .map(|term| {
                let affine_exponents = term.exponents();
                let mut stratum_exponents = [0; BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT];
                stratum_exponents[..AFFINE_P3_VARIABLE_COUNT].copy_from_slice(&affine_exponents);
                (term.coefficient(), stratum_exponents)
            })
            .collect(),
    )
}

fn quadratic_polynomial_to_big_quadratic<const N: usize>(
    polynomial: SparsePolynomial<QuadraticRational, N>,
) -> SparsePolynomial<BigQuadraticRational, N> {
    polynomial.map_coefficients(|coefficient| BigQuadraticRational::from(*coefficient))
}

fn tau() -> Q5 {
    (q(1) + Q5::sqrt(5)) / q(2)
}

fn tau_bar() -> Q5 {
    (q(1) - Q5::sqrt(5)) / q(2)
}

fn q(value: i64) -> Q5 {
    Q5::from_i64(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn barth_polynomial_has_degree_six_over_sqrt_five() {
        let polynomial = barth_sextic_polynomial();
        assert_eq!(polynomial.degree(), 6);
        assert_eq!(polynomial.terms().len(), 17);
        assert_eq!(tau() * tau(), tau() + q(1));
        assert_eq!(tau() + tau_bar(), q(1));
        assert_eq!(tau() * tau_bar(), q(-1));
    }

    #[test]
    fn table_nodes_have_expected_class_counts_and_are_projectively_distinct() {
        let nodes = barth_nodes();
        assert_eq!(barth_nodes_a().len(), BARTH_NODE_A_COUNT);
        assert_eq!(barth_nodes_b().len(), BARTH_NODE_B_COUNT);
        assert_eq!(barth_nodes_c().len(), BARTH_NODE_C_COUNT);
        assert_eq!(nodes.len(), BARTH_NODE_COUNT);
        assert_eq!(projective_unique_count(&nodes), BARTH_NODE_COUNT);
        assert!(
            barth_nodes_a()
                .iter()
                .all(|point| point.p3_coords()[0].is_zero())
        );
        assert!(
            barth_nodes_b()
                .iter()
                .chain(barth_nodes_c().iter())
                .all(|point| !point.p3_coords()[0].is_zero())
        );
    }

    #[test]
    fn a5_generators_make_single_orbits_for_each_node_class() {
        assert_eq!(barth_a5_orbit_indices(BarthNodeClass::A).len(), 15);
        assert_eq!(barth_a5_orbit_indices(BarthNodeClass::B).len(), 30);
        assert_eq!(barth_a5_orbit_indices(BarthNodeClass::C).len(), 20);
        assert_eq!(projective_unique_count(&barth_nodes_a_orbit()), 15);
        assert_eq!(projective_unique_count(&barth_nodes_b_orbit()), 30);
        assert_eq!(projective_unique_count(&barth_nodes_c_orbit()), 20);
    }

    #[test]
    fn a5_orbit_route_matches_table_transcription_oracle() {
        assert_same_projective_set(&barth_nodes_a_orbit(), &barth_nodes_a());
        assert_same_projective_set(&barth_nodes_b_orbit(), &barth_nodes_b());
        assert_same_projective_set(&barth_nodes_c_orbit(), &barth_nodes_c());
    }

    #[test]
    fn a5_generator_action_matches_mid_and_centre_line_labels() {
        for class in [BarthNodeClass::A, BarthNodeClass::B, BarthNodeClass::C] {
            let records = records_of_class(class);
            for generator in [BarthA5Generator::Sigma, BarthA5Generator::Tau] {
                let node_permutation = barth_a5_node_permutation(class, generator);
                for (source_index, source) in records.iter().enumerate() {
                    let target = &records[node_permutation[source_index]];
                    assert_eq!(
                        barth_line_label_after_generator(source.line(), generator),
                        barth_line_label(target.line()),
                        "{} under {:?}",
                        source.label(),
                        generator
                    );
                }
            }
        }
    }

    #[test]
    fn all_table_nodes_are_ordinary_double_points() {
        let surface = barth_sextic();
        for node in barth_node_records() {
            let verification = surface.verify_node(node.point().clone());
            assert!(
                verification.ordinary_double_point(),
                "{} failed: F={}, grad={:?}, hessian rank={}",
                node.label(),
                verification.value(),
                verification.gradient(),
                verification.hessian_rank()
            );
        }
    }

    #[test]
    fn mid_lines_have_three_collinear_nodes() {
        let groups = barth_mid_line_node_groups();
        assert_eq!(groups.len(), BARTH_MID_LINE_COUNT);
        for (line, points) in groups {
            assert_eq!(points.len(), 3, "{line}");
            assert_eq!(projective_unique_count(&points), 3, "{line}");
            assert_eq!(points_span_rank(&points), 2, "{line}");
        }
    }

    #[test]
    fn centre_lines_have_two_distinct_nodes() {
        let groups = barth_centre_line_node_groups();
        assert_eq!(groups.len(), BARTH_CENTRE_LINE_COUNT);
        for (line, points) in groups {
            assert_eq!(points.len(), 2, "{line}");
            assert_eq!(projective_unique_count(&points), 2, "{line}");
            assert_eq!(points_span_rank(&points), 2, "{line}");
        }
    }

    #[test]
    fn projective_support_strata_are_well_formed() {
        for support_mask in 1..=BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT {
            let stratum = barth_projective_support_stratum_generators(support_mask as u8);
            assert_eq!(
                stratum.generators().len(),
                AFFINE_P3_VARIABLE_COUNT + 2 + AFFINE_P3_VARIABLE_COUNT
                    - (stratum.support().projective_variables().len() - 1)
            );
            assert!(
                stratum
                    .generators()
                    .iter()
                    .all(|generator| generator.degree() <= 6)
            );
        }
    }

    #[test]
    fn support_groebner_certificates_verify_projective_length_sixty_five() {
        let certificate = barth_singular_scheme_certificate().expect("certificates parse");
        let verifications = certificate
            .support_strata()
            .iter()
            .map(|stratum| stratum.verify())
            .collect::<Vec<_>>();

        for verification in &verifications {
            assert!(
                verification.verified(),
                "support {} failed: {:?}",
                verification.support_mask(),
                verification
            );
        }

        assert_eq!(
            verifications
                .iter()
                .map(|verification| verification.expected_quotient_length())
                .collect::<Vec<_>>(),
            BARTH_PROJECTIVE_SUPPORT_STRATUM_LENGTHS
        );
        assert_eq!(
            certificate
                .support_lifts()
                .iter()
                .map(|lift| (lift.source_count(), lift.target_count()))
                .collect::<Vec<_>>(),
            certificate
                .support_strata()
                .iter()
                .map(|stratum| {
                    (
                        stratum.certificate().generators().len(),
                        stratum.certificate().basis().len(),
                    )
                })
                .collect::<Vec<_>>()
        );
        assert_eq!(certificate.verified_projective_length(), Some(65));
        assert_eq!(certificate.verified_reduced_ordinary_node_count(), Some(65));
    }

    fn assert_same_projective_set(lhs: &[ProjectivePoint<Q5>], rhs: &[ProjectivePoint<Q5>]) {
        assert_eq!(lhs.len(), rhs.len());
        assert!(lhs.iter().all(|point| rhs.iter().any(|seen| seen == point)));
        assert!(rhs.iter().all(|point| lhs.iter().any(|seen| seen == point)));
    }
}
