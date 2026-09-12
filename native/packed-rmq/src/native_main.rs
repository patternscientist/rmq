use packed_rmq::native::{NativeRuntime, MAX_IMAGE_BYTES};
use std::io::Read;

const USAGE: &str = "usage: packed-rmq-native load IMAGE | query IMAGE LEFT_HEX RIGHT_HEX FUEL READS [REPEAT]";

fn hex_bytes(text: &str) -> Result<Vec<u8>, String> {
    if text.len() > 1024 || text.len() % 2 != 0 { return Err("invalid endpoint hex".into()); }
    fn nibble(byte: u8) -> Option<u8> {
        match byte {
            b'0'..=b'9' => Some(byte - b'0'),
            b'a'..=b'f' => Some(byte - b'a' + 10),
            b'A'..=b'F' => Some(byte - b'A' + 10),
            _ => None,
        }
    }
    text.as_bytes().chunks_exact(2).map(|pair| {
        let high = nibble(pair[0]).ok_or_else(|| "invalid endpoint hex".to_owned())?;
        let low = nibble(pair[1]).ok_or_else(|| "invalid endpoint hex".to_owned())?;
        Ok(high * 16 + low)
    }).collect()
}

fn natural(text: &str, name: &str) -> Result<usize, String> {
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!("invalid {name}"));
    }
    text.parse().map_err(|_| format!("invalid {name}"))
}

fn execute() -> Result<(), String> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let is_load = args.len() == 2 && args[0] == "load";
    let is_query = matches!(args.len(), 6 | 7) && args[0] == "query";
    if !is_load && !is_query { return Err(USAGE.into()); }
    let query = if is_query {
        let left = hex_bytes(&args[2])?;
        let right = hex_bytes(&args[3])?;
        let fuel = natural(&args[4], "fuel")?;
        let reads = match args[5].as_str() {
            "0" => false,
            "1" => true,
            _ => return Err("reads must be 0 or 1".into()),
        };
        let repeat = if args.len() == 7 { natural(&args[6], "repeat")? } else { 1 };
        if !(1..=16).contains(&repeat) { return Err("repeat must be between 1 and 16".into()); }
        Some((left, right, fuel, reads, repeat))
    } else { None };
    let metadata = std::fs::metadata(&args[1]).map_err(|error| error.to_string())?;
    if metadata.len() > MAX_IMAGE_BYTES as u64 { return Err("image byte limit".into()); }
    let mut bytes = Vec::new();
    std::fs::File::open(&args[1]).map_err(|error| error.to_string())?
        .take(MAX_IMAGE_BYTES as u64 + 1).read_to_end(&mut bytes)
        .map_err(|error| error.to_string())?;
    if bytes.len() > MAX_IMAGE_BYTES { return Err("image byte limit".into()); }
    let runtime = NativeRuntime::new()?;
    let mut image = runtime.load(&bytes)?;
    drop(bytes);
    if let Some((left, right, fuel, reads, repeat)) = query {
        for _ in 0..repeat {
            print!("{}", image.query(&left, &right, fuel, reads)?);
        }
    } else {
        println!("loaded {}", image.word_bytes());
    }
    Ok(())
}

fn main() {
    if let Err(error) = execute() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}
