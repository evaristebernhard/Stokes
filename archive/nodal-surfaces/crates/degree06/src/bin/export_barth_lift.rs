use degree06::{
    BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT, BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT,
    barth_projective_support_stratum_generators,
};
use nodal_core::{QuadraticRational, Rational, SparsePolynomial};
use std::env;
use std::process;

fn main() {
    let args: Vec<_> = env::args().collect();
    let support_mask = match parse_args(&args) {
        Ok(mask) => mask,
        Err(message) => {
            eprintln!("{message}");
            eprintln!("usage: export_barth_lift <support-mask 1..15>");
            process::exit(2);
        }
    };

    let stratum = barth_projective_support_stratum_generators(support_mask);
    print_lift_script(
        &format!("barth_support_{support_mask:02}_lift"),
        stratum.generators(),
        &["u0", "u1", "u2", "loc"],
    );
}

fn parse_args(args: &[String]) -> Result<u8, String> {
    if args.len() != 2 {
        return Err("expected support mask".to_string());
    }

    let support_mask = args[1]
        .parse::<u8>()
        .map_err(|error| format!("invalid support mask `{}`: {error}", args[1]))?;
    if !(1..=BARTH_PROJECTIVE_SUPPORT_STRATUM_COUNT as u8).contains(&support_mask) {
        return Err("support mask must be between 1 and 15".to_string());
    }

    Ok(support_mask)
}

fn print_lift_script(
    certificate_name: &str,
    generators: &[SparsePolynomial<QuadraticRational, BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>],
    variables: &[&str; BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT],
) {
    println!("// Generated from the Catanese/Barth sextic model.");
    println!("// Groebner basis lift witness: G[j] = sum_i L[i,j] * I[i].");
    println!("ring r = (0,t),({}),dp;", variables.join(","));
    println!("minpoly = t^2-5;");
    println!("option(redSB);");
    print_certificate_proc();
    for (index, generator) in generators.iter().enumerate() {
        println!(
            "poly f{} = {};",
            index + 1,
            singular_polynomial(generator, variables)
        );
    }
    let generator_names = (1..=generators.len())
        .map(|index| format!("f{index}"))
        .collect::<Vec<_>>()
        .join(",");
    println!("ideal I = {generator_names};");
    println!("ideal G = std(I);");
    println!("matrix L = lift(I,G);");
    println!("print(\"# {certificate_name}\");");
    println!("print(\"# coefficient_field Qsqrt5\");");
    println!("print(\"# singular_order dp\");");
    println!("print(\"source_count {}\");", generators.len());
    println!("print(\"target_count \"+string(size(G)));");
    println!("int target_index;");
    println!("int source_index;");
    println!("for (target_index = 1; target_index <= size(G); target_index = target_index + 1) {{");
    println!("  print(\"target \"+string(target_index - 1));");
    println!(
        "  for (source_index = 1; source_index <= ncols(I); source_index = source_index + 1) {{"
    );
    println!("    printCertificatePoly(L[source_index,target_index]);");
    println!("  }}");
    println!("}}");
    println!("quit;");
}

fn print_certificate_proc() {
    println!("proc printCertificatePoly(poly p)");
    println!("{{");
    println!("  print(\"poly\");");
    println!("  number c;");
    println!("  intvec e;");
    println!("  string line;");
    println!("  int variable_index;");
    println!("  while (p != 0)");
    println!("  {{");
    println!("    c = leadcoef(p);");
    println!("    e = leadexp(p);");
    println!("    line = string(c);");
    println!(
        "    for (variable_index = 1; variable_index <= nvars(basering); variable_index = variable_index + 1)"
    );
    println!("    {{");
    println!("      line = line + \" \" + string(e[variable_index]);");
    println!("    }}");
    println!("    print(line);");
    println!("    p = p - lead(p);");
    println!("  }}");
    println!("  print(\"end\");");
    println!("}}");
    println!();
}

fn singular_polynomial(
    polynomial: &SparsePolynomial<QuadraticRational, BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT>,
    variables: &[&str; BARTH_PROJECTIVE_STRATUM_VARIABLE_COUNT],
) -> String {
    let terms = polynomial.terms();
    if terms.is_empty() {
        return "0".to_string();
    }

    terms
        .iter()
        .map(|term| {
            let coefficient = singular_quadratic_rational(term.coefficient());
            let monomial = term
                .exponents()
                .iter()
                .enumerate()
                .filter_map(|(index, &exponent)| match exponent {
                    0 => None,
                    1 => Some(variables[index].to_string()),
                    _ => Some(format!("{}^{}", variables[index], exponent)),
                })
                .collect::<Vec<_>>();

            if monomial.is_empty() {
                format!("({coefficient})")
            } else {
                format!("({coefficient})*{}", monomial.join("*"))
            }
        })
        .collect::<Vec<_>>()
        .join(" + ")
}

fn singular_quadratic_rational(value: QuadraticRational) -> String {
    let rational = value.rational();
    let irrational = value.irrational();
    if irrational.is_zero() {
        return rational.to_string();
    }

    let mut parts = Vec::new();
    if !irrational.is_zero() {
        parts.push(format_rational_t(irrational));
    }
    if !rational.is_zero() {
        parts.push(rational.to_string());
    }

    parts.join("+").replace("+-", "-").replace("+ -", "-")
}

fn format_rational_t(value: Rational) -> String {
    if value == Rational::ONE {
        "t".to_string()
    } else if value == -Rational::ONE {
        "-t".to_string()
    } else {
        format!("{value}t")
    }
}
