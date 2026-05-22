use degree07::{
    CubicAlphaRational, LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT,
    LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT, labs_projective_support_stratum_generators,
};
use nodal_core::{Rational, SparsePolynomial};
use std::env;
use std::process;

type PolynomialA4 = SparsePolynomial<CubicAlphaRational, LABS_PROJECTIVE_STRATUM_VARIABLE_COUNT>;

fn main() {
    let args: Vec<_> = env::args().collect();
    let support_mask = match parse_args(&args) {
        Ok(mask) => mask,
        Err(message) => {
            eprintln!("{message}");
            eprintln!("usage: export_labs_projective_strata <support-mask 1..15>");
            process::exit(2);
        }
    };

    let stratum = labs_projective_support_stratum_generators(support_mask);
    let variables = ["u0", "u1", "u2", "loc"];
    let affine_indices = stratum.affine_projective_indices();

    println!("ring r = (0,a),({}),dp;", variables.join(","));
    println!("minpoly = 7*a^3+7*a+1;");
    println!("print(\"# generated_by export_labs_projective_strata\");");
    println!("// Generated from the Labs 99-nodal septic model.");
    println!(
        "// Projective support mask {support_mask}; chart x{} = 1.",
        stratum.chart_variable()
    );
    println!("option(redSB);");
    print_certificate_proc();
    for (index, generator) in stratum.generators().iter().enumerate() {
        println!(
            "poly f{} = {};",
            index + 1,
            singular_polynomial(generator, &variables)
        );
    }
    let generator_names = (1..=stratum.generators().len())
        .map(|index| format!("f{index}"))
        .collect::<Vec<_>>()
        .join(",");
    println!("ideal I = {generator_names};");
    println!("ideal G = std(I);");
    println!("print(\"# labs_support_mask {support_mask}\");");
    println!("print(\"# chart_variable {}\");", stratum.chart_variable());
    println!(
        "print(\"# affine_projective_indices {} {} {}\");",
        affine_indices[0], affine_indices[1], affine_indices[2]
    );
    println!("print(\"# coefficient_field Qalpha_7a3_7a_1\");");
    println!("print(\"# singular_order dp\");");
    println!("print(\"# basis_size \"+string(size(G)));");
    println!("print(\"# vdim \"+string(vdim(G)));");
    println!("print(\"order grevlex\");");
    println!("print(\"\");");
    println!("print(\"generators\");");
    for index in 1..=stratum.generators().len() {
        println!("printCertificatePoly(f{index});");
    }
    println!("print(\"\");");
    println!("print(\"basis\");");
    println!("for (int i = 1; i <= size(G); i = i + 1) {{");
    println!("  printCertificatePoly(G[i]);");
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

fn parse_args(args: &[String]) -> Result<u8, String> {
    if args.len() != 2 {
        return Err("expected support mask".to_string());
    }

    let support_mask = args[1]
        .parse::<u8>()
        .map_err(|error| format!("invalid support mask `{}`: {error}", args[1]))?;
    if !(1..=LABS_PROJECTIVE_SUPPORT_STRATUM_COUNT as u8).contains(&support_mask) {
        return Err("support mask must be between 1 and 15".to_string());
    }

    Ok(support_mask)
}

fn singular_polynomial(polynomial: &PolynomialA4, variables: &[&str; 4]) -> String {
    let terms = polynomial.terms();
    if terms.is_empty() {
        return "0".to_string();
    }

    terms
        .iter()
        .map(|term| {
            let coefficient = singular_cubic_alpha_rational(term.coefficient());
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

fn singular_cubic_alpha_rational(value: CubicAlphaRational) -> String {
    let [constant, alpha, alpha_squared] = value.coefficients();
    let mut parts = Vec::new();
    if !alpha_squared.is_zero() {
        parts.push(format_rational_alpha_power(alpha_squared, "a^2"));
    }
    if !alpha.is_zero() {
        parts.push(format_rational_alpha_power(alpha, "a"));
    }
    if !constant.is_zero() {
        parts.push(constant.to_string());
    }

    if parts.is_empty() {
        "0".to_string()
    } else {
        parts.join("+").replace("+-", "-").replace("+ -", "-")
    }
}

fn format_rational_alpha_power(value: Rational, power: &str) -> String {
    if value == Rational::ONE {
        power.to_string()
    } else if value == -Rational::ONE {
        format!("-{power}")
    } else {
        format!("{value}*{power}")
    }
}
