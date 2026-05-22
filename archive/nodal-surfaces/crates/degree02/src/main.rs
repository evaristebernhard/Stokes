fn main() {
    let examples = [
        (
            "smooth quadric: x^2 + y^2 + z^2 + w^2 = 0",
            degree02::smooth_quadric(),
        ),
        (
            "quadric cone: x^2 + y^2 - z^2 = 0",
            degree02::standard_quadric_cone(),
        ),
        (
            "reducible quadric: x^2 - y^2 = 0",
            degree02::reducible_two_planes(),
        ),
    ];

    for (name, quadric) in examples {
        println!("{name}");
        println!("  {}", quadric.classify());
    }
}
