use nodal_core::{Matrix, ProjectivePoint, Rational};
use std::fmt;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct QuadricForm {
    matrix: Matrix,
}

impl QuadricForm {
    pub fn from_symmetric_matrix(entries: [[i64; 4]; 4]) -> Self {
        for (row, row_entries) in entries.iter().enumerate() {
            for (col, &entry) in row_entries.iter().enumerate() {
                assert_eq!(
                    entry, entries[col][row],
                    "quadratic form matrix must be symmetric"
                );
            }
        }

        Self {
            matrix: Matrix::from_rows(
                entries
                    .into_iter()
                    .map(|row| row.into_iter().map(Rational::from).collect())
                    .collect(),
            ),
        }
    }

    pub fn classify(&self) -> QuadricClassification {
        let rank = self.matrix.rank();
        let kernel = self.matrix.nullspace();

        match rank {
            4 => QuadricClassification::Smooth { rank },
            3 => QuadricClassification::OrdinaryQuadricCone {
                rank,
                node: ProjectivePoint::new(kernel[0].clone()),
            },
            _ => QuadricClassification::NonIsolatedSingularLocus {
                rank,
                projective_dimension: kernel.len().saturating_sub(1),
                basis: kernel.into_iter().map(ProjectivePoint::new).collect(),
            },
        }
    }

    pub fn gradient_matrix(&self) -> &Matrix {
        &self.matrix
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum QuadricClassification {
    Smooth {
        rank: usize,
    },
    OrdinaryQuadricCone {
        rank: usize,
        node: ProjectivePoint,
    },
    NonIsolatedSingularLocus {
        rank: usize,
        projective_dimension: usize,
        basis: Vec<ProjectivePoint>,
    },
}

impl QuadricClassification {
    pub fn node_count(&self) -> Option<usize> {
        match self {
            QuadricClassification::Smooth { .. } => Some(0),
            QuadricClassification::OrdinaryQuadricCone { .. } => Some(1),
            QuadricClassification::NonIsolatedSingularLocus { .. } => None,
        }
    }
}

impl fmt::Display for QuadricClassification {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QuadricClassification::Smooth { rank } => {
                write!(f, "smooth quadric, matrix rank {rank}, nodes = 0")
            }
            QuadricClassification::OrdinaryQuadricCone { rank, node } => write!(
                f,
                "ordinary quadric cone, matrix rank {rank}, unique node at {node}"
            ),
            QuadricClassification::NonIsolatedSingularLocus {
                rank,
                projective_dimension,
                basis,
            } => {
                let basis = basis
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(
                    f,
                    "singular locus is non-isolated, matrix rank {rank}, projective dimension {projective_dimension}, kernel basis {basis}"
                )
            }
        }
    }
}

pub fn standard_quadric_cone() -> QuadricForm {
    // x^2 + y^2 - z^2 = 0 in P^3, with vertex [0:0:0:1].
    QuadricForm::from_symmetric_matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, -1, 0], [0, 0, 0, 0]])
}

pub fn smooth_quadric() -> QuadricForm {
    QuadricForm::from_symmetric_matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]])
}

pub fn reducible_two_planes() -> QuadricForm {
    // x^2 - y^2 = 0 is two planes; the singular locus is their intersection line.
    QuadricForm::from_symmetric_matrix([[1, 0, 0, 0], [0, -1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]])
}

#[cfg(test)]
mod tests {
    use super::{
        QuadricClassification, reducible_two_planes, smooth_quadric, standard_quadric_cone,
    };

    #[test]
    fn smooth_quadric_has_no_nodes() {
        let classification = smooth_quadric().classify();
        assert_eq!(classification.node_count(), Some(0));
        assert!(matches!(
            classification,
            QuadricClassification::Smooth { rank: 4 }
        ));
    }

    #[test]
    fn rank_three_quadric_is_one_node_cone() {
        let classification = standard_quadric_cone().classify();
        assert_eq!(classification.node_count(), Some(1));
        assert!(matches!(
            classification,
            QuadricClassification::OrdinaryQuadricCone { rank: 3, .. }
        ));
        assert!(classification.to_string().contains("[0:0:0:1]"));
    }

    #[test]
    fn rank_two_quadric_has_non_isolated_singular_locus() {
        let classification = reducible_two_planes().classify();
        assert_eq!(classification.node_count(), None);
        assert!(matches!(
            classification,
            QuadricClassification::NonIsolatedSingularLocus {
                rank: 2,
                projective_dimension: 1,
                ..
            }
        ));
    }
}
