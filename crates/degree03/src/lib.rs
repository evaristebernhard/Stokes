use nodal_core::{HomogeneousPolynomialP3, Matrix, ProjectivePoint, Rational};
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CubicSurface {
    polynomial: HomogeneousPolynomialP3,
}

impl CubicSurface {
    pub fn new(polynomial: HomogeneousPolynomialP3) -> Self {
        assert_eq!(polynomial.degree(), 3, "expected a cubic surface");
        Self { polynomial }
    }

    pub fn polynomial(&self) -> &HomogeneousPolynomialP3 {
        &self.polynomial
    }

    pub fn verify_node(&self, point: ProjectivePoint) -> NodeVerification {
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
                && gradient.into_iter().all(Rational::is_zero)
                && hessian_rank == 3,
            hessian,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NodeVerification {
    point: ProjectivePoint,
    value: Rational,
    gradient: [Rational; 4],
    hessian_rank: usize,
    ordinary_double_point: bool,
    hessian: Matrix,
}

impl NodeVerification {
    pub fn point(&self) -> &ProjectivePoint {
        &self.point
    }

    pub fn value(&self) -> Rational {
        self.value
    }

    pub fn gradient(&self) -> [Rational; 4] {
        self.gradient
    }

    pub fn hessian_rank(&self) -> usize {
        self.hessian_rank
    }

    pub fn ordinary_double_point(&self) -> bool {
        self.ordinary_double_point
    }

    pub fn hessian(&self) -> &Matrix {
        &self.hessian
    }
}

impl fmt::Display for NodeVerification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: F = {}, gradient = [{}, {}, {}, {}], Hessian rank = {}, ordinary node = {}",
            self.point,
            self.value,
            self.gradient[0],
            self.gradient[1],
            self.gradient[2],
            self.gradient[3],
            self.hessian_rank,
            self.ordinary_double_point
        )
    }
}

pub fn cayley_cubic() -> CubicSurface {
    // Variable order is [x:y:z:w]. This is e_3(x,y,z,w).
    CubicSurface::new(HomogeneousPolynomialP3::from_terms(vec![
        (1.into(), [1, 1, 1, 0]),
        (1.into(), [1, 1, 0, 1]),
        (1.into(), [1, 0, 1, 1]),
        (1.into(), [0, 1, 1, 1]),
    ]))
}

pub fn cayley_coordinate_nodes() -> Vec<ProjectivePoint> {
    cayley_singular_points()
}

pub fn cayley_singular_points() -> Vec<ProjectivePoint> {
    vec![
        p3_point([1, 0, 0, 0]),
        p3_point([0, 1, 0, 0]),
        p3_point([0, 0, 1, 0]),
        p3_point([0, 0, 0, 1]),
    ]
}

pub fn cayley_node_verifications() -> Vec<NodeVerification> {
    let surface = cayley_cubic();
    cayley_coordinate_nodes()
        .into_iter()
        .map(|point| surface.verify_node(point))
        .collect()
}

pub fn cayley_node_count() -> usize {
    cayley_singular_points().len()
}

/// In the chart x=1, the Cayley gradient equations reduce to two symmetric
/// branches; checking the full gradient leaves only the chart origin.
pub fn cayley_affine_chart_singular_solutions() -> Vec<[Rational; 3]> {
    let zero = Rational::ZERO;
    let minus_two = Rational::from_i64(-2);

    [[zero, zero, zero], [minus_two, minus_two, minus_two]]
        .into_iter()
        .filter(|coords| {
            cayley_affine_chart_gradient(*coords)
                .into_iter()
                .all(Rational::is_zero)
        })
        .collect()
}

fn cayley_affine_chart_gradient(coords: [Rational; 3]) -> [Rational; 4] {
    let [a, b, c] = coords;

    [
        a * b + a * c + b * c,
        b + c + b * c,
        a + c + a * c,
        a + b + a * b,
    ]
}

fn p3_point(coords: [i64; 4]) -> ProjectivePoint {
    ProjectivePoint::new(coords.into_iter().map(Rational::from).collect())
}

#[cfg(test)]
mod tests {
    use super::{cayley_coordinate_nodes, cayley_cubic, cayley_node_count};
    use nodal_core::{ProjectivePoint, Rational};

    #[test]
    fn cayley_cubic_has_degree_three() {
        let surface = cayley_cubic();

        assert_eq!(surface.polynomial().degree(), 3);
        assert_eq!(surface.polynomial().terms().len(), 4);
    }

    #[test]
    fn coordinate_points_are_ordinary_double_points() {
        let surface = cayley_cubic();

        for point in cayley_coordinate_nodes() {
            let verification = surface.verify_node(point);
            assert_eq!(verification.value(), Rational::ZERO);
            assert_eq!(verification.gradient(), [Rational::ZERO; 4]);
            assert_eq!(verification.hessian_rank(), 3);
            assert!(verification.ordinary_double_point());
        }
    }

    #[test]
    fn cayley_certificate_lists_four_nodes() {
        let nodes = cayley_coordinate_nodes();

        assert_eq!(cayley_node_count(), 4);
        assert_eq!(nodes.len(), 4);
        assert_eq!(nodes[0].to_string(), "[1:0:0:0]");
        assert_eq!(nodes[1].to_string(), "[0:1:0:0]");
        assert_eq!(nodes[2].to_string(), "[0:0:1:0]");
        assert_eq!(nodes[3].to_string(), "[0:0:0:1]");
    }

    #[test]
    fn affine_chart_certificate_has_only_the_origin() {
        assert_eq!(
            super::cayley_affine_chart_singular_solutions(),
            vec![[Rational::ZERO, Rational::ZERO, Rational::ZERO]]
        );
    }

    #[test]
    fn a_general_point_is_not_singular() {
        let surface = cayley_cubic();
        let point = ProjectivePoint::new(vec![1.into(), 1.into(), 1.into(), 1.into()]);

        assert!(!surface.polynomial().is_singular_at(&point));
        assert!(!surface.polynomial().is_ordinary_double_point_at(&point));
    }
}
