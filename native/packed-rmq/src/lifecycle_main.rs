use packed_rmq::lifecycle::{Category, Error, LifecycleRuntime, Model, Owner, SignedInteger};

fn require(condition: bool) -> Result<(), Error> {
    if condition { Ok(()) } else { Err(Error::InvalidForeignResult) }
}

fn check_owner(owner: &Owner<'_>, expected_count: usize) -> Result<(), Error> {
    let info = owner.inspect()?;
    require(info.count == expected_count && info.exclusive_owner == 1 &&
        info.exact_capacities == 1 && info.no_retained_operational_roots == 1)?;
    require(info.arrays.iter().all(|array| array.initialized == array.capacity))?;
    require(info.arrays[0].initialized == 8273 && info.arrays[2].initialized == 0 &&
        info.arrays[3].initialized == 0)
}

fn run_owner(model: Model) -> Result<(), Error> {
    let runtime = LifecycleRuntime::new()?;
    let profile = runtime.profile(4)?;
    let left = profile.endpoint(&[0])?;
    let right = profile.endpoint(&[4])?;
    // The input vectors and borrowed descriptors disappear at this boundary.
    let (mut owner, first) = {
        let mut wide = vec![0; 17];
        wide[0] = 7;
        wide[16] = 4; // 2^130 + 7, independently chosen expected minima.
        let values = match model {
            Model::Word => vec![(false, vec![3]), (true, vec![1]), (true, vec![1]), (false, vec![7])],
            Model::Comparison => vec![(true, wide.clone()), (false, vec![5]), (true, wide), (false, vec![0])],
        };
        let input: Vec<_> = values.iter().map(|(negative, bytes)|
            SignedInteger::new(*negative, bytes)).collect::<Result<_, _>>()?;
        runtime.build_first(model, &input, &left, &right, false)?
    };
    require(first.index_magnitude() == Some(vec![if model == Model::Word { 1 } else { 0 }]))?;
    require(first.observation.is_none())?;
    drop(first);
    check_owner(&owner, 4)?;
    let produced_profile = owner.profile()?;
    require(produced_profile == profile)?;

    let suffix = owner.query(&produced_profile.endpoint(&[2])?, &right, true)?;
    require(suffix.index_magnitude() == Some(vec![2]))?;
    let observed = suffix.observation.as_ref().ok_or(Error::InvalidForeignResult)?;
    require(!observed.counter(Category::Steps)?.is_zero())?;
    let reads = observed.read_count()?;
    if reads != 0 { let _receipt = observed.read(0)?; }
    drop(suffix);
    check_owner(&owner, 4)?;

    let invalid = owner.query(&produced_profile.endpoint(&[3])?,
        &produced_profile.endpoint(&[1])?, false)?;
    require(invalid.index_magnitude().is_none())?;
    drop(invalid);
    check_owner(&owner, 4)?;

    let final_answer = owner.query(&left, &produced_profile.endpoint(&[2])?, false)?;
    require(final_answer.index_magnitude() == Some(vec![if model == Model::Word { 1 } else { 0 }]))?;
    drop(owner);
    // Answer storage is an independent result object and remains readable.
    require(!final_answer.answer.is_zero())?;
    drop(final_answer);
    Ok(())
}

fn execute(mode: &str) -> Result<(), Error> {
    match mode {
        "smoke" | "word" => run_owner(Model::Word),
        "comparison" => run_owner(Model::Comparison),
        "initialization-failure" => {
            std::env::set_var("PACKED_LIFECYCLE_FAIL_INIT", "1");
            require(matches!(LifecycleRuntime::new(), Err(Error::Initialization)))?;
            std::env::remove_var("PACKED_LIFECYCLE_FAIL_INIT");
            require(matches!(LifecycleRuntime::new(), Err(Error::RuntimeAlreadyClaimed)))
        }
        _ => Err(Error::Format),
    }
}

fn main() {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    if arguments.len() != 1 {
        eprintln!("usage: packed-rmq-lifecycle smoke|word|comparison|initialization-failure");
        std::process::exit(2);
    }
    if let Err(error) = execute(&arguments[0]) {
        eprintln!("LIFE-NATIVE1 RUST {} FAIL {error}", arguments[0]);
        std::process::exit(1);
    }
    println!("LIFE-NATIVE1 RUST {} PASS", arguments[0]);
}
