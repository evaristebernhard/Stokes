use degree05::{
    TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT, togliatti_projective_support_stratum_generators,
};
use nodal_core::{Rational, SparsePolynomial};
use std::env;
use std::fmt;
use std::process;

type PolynomialA4 = SparsePolynomial<Rational, TOGLIATTI_PROJECTIVE_STRATUM_VARIABLE_COUNT>;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ExportOrder {
    Lex,
    GrevLex,
}

impl ExportOrder {
    fn singular_name(self) -> &'static str {
        match self {
            Self::Lex => "lp",
            Self::GrevLex => "dp",
        }
    }

    fn certificate_name(self) -> &'static str {
        match self {
            Self::Lex => "lex",
            Self::GrevLex => "grevlex",
        }
    }
}

impl fmt::Display for ExportOrder {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.certificate_name())
    }
}

fn main() {
    let args: Vec<_> = env::args().collect();
    let (support_mask, order) = match parse_args(&args) {
        Ok(config) => config,
        Err(message) => {
            eprintln!("{message}");
            eprintln!(
                "usage: export_togliatti_projective_strata <support-mask 1..15> [lex|grevlex]"
            );
            process::exit(2);
        }
    };

    let stratum = togliatti_projective_support_stratum_generators(support_mask);
    let variables = ["u0", "u1", "u2", "tau"];
    let support_variables = stratum
        .support()
        .projective_variables()
        .into_iter()
        .map(|variable| format!("x{variable}"))
        .collect::<Vec<_>>()
        .join(",");
    let affine_indices = stratum.affine_projective_indices();

    println!("// Generated from crates/degree05 Catanese Proposition 130 determinant model.");
    println!(
        "// Projective support mask {support_mask}; support {{{support_variables}}}; chart x{} = 1.",
        stratum.chart_variable()
    );
    println!(
        "// Affine variables ({}, {}, {}) correspond to projective variables ({}, {}, {}).",
        variables[0],
        variables[1],
        variables[2],
        affine_indices[0],
        affine_indices[1],
        affine_indices[2]
    );
    println!(
        "ring r = 0,({}),{};",
        variables.join(","),
        order.singular_name()
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
    println!("print(\"# projective_support_mask {support_mask}\");");
    println!("print(\"# chart_variable {}\");", stratum.chart_variable());
    println!(
        "print(\"# affine_projective_indices {} {} {}\");",
        affine_indices[0], affine_indices[1], affine_indices[2]
    );
    println!("print(\"# singular_order {}\");", order.singular_name());
    println!("print(\"# basis_size \"+string(size(G)));");
    println!("print(\"# vdim \"+string(vdim(G)));");
    println!("print(\"order {}\");", order.certificate_name());
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
    println!("  int i;");
    println!("  while (p != 0)");
    println!("  {{");
    println!("    c = leadcoef(p);");
    println!("    e = leadexp(p);");
    println!("    line = string(c);");
    println!("    for (i = 1; i <= nvars(basering); i = i + 1)");
    println!("    {{");
    println!("      line = line + \" \" + string(e[i]);");
    println!("    }}");
    println!("    print(line);");
    println!("    p = p - lead(p);");
    println!("  }}");
    println!("  print(\"end\");");
    println!("}}");
    println!();
}

fn parse_args(args: &[String]) -> Result<(u8, ExportOrder), String> {
    if args.len() < 2 || args.len() > 3 {
        return Err("expected support mask and optional order".to_string());
    }

    let support_mask = args[1]
        .parse::<u8>()
        .map_err(|error| format!("invalid support mask `{}`: {error}", args[1]))?;
    if !(1..=15).contains(&support_mask) {
        return Err("support mask must be between 1 and 15".to_string());
    }

    let order = if let Some(order) = args.get(2) {
        match order.to_ascii_lowercase().as_str() {
            "lex" => ExportOrder::Lex,
            "grevlex" => ExportOrder::GrevLex,
            _ => return Err(format!("unsupported order `{order}`; use lex or grevlex")),
        }
    } else {
        ExportOrder::GrevLex
    };

    Ok((support_mask, order))
}

fn singular_polynomial(polynomial: &PolynomialA4, variables: &[&str; 4]) -> String {
    let terms = polynomial.terms();
    if terms.is_empty() {
        return "0".to_string();
    }

    terms
        .iter()
        .map(|term| {
            let coefficient = term.coefficient();
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
