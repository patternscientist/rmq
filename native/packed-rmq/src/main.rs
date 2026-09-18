use packed_rmq::RouteRuntime;

fn execute() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() != 3 || !matches!(args[2].as_str(), "reads" | "quiet") {
        return Err("usage: packed-rmq-route PROGRAM FIXTURE reads|quiet".into());
    }
    let program = std::fs::read_to_string(&args[0]).map_err(|e| e.to_string())?;
    let fixture = std::fs::read_to_string(&args[1]).map_err(|e| e.to_string())?;
    let output = RouteRuntime::new()?.evaluate(&program, &fixture, args[2] == "reads")?;
    print!("{output}");
    if output.starts_with("ERROR ") { return Err("Lean parser rejected input".into()); }
    Ok(())
}

fn main() {
    if let Err(e) = execute() {
        eprintln!("{e}");
        std::process::exit(2);
    }
}
