use packed_rmq::lifecycle::{Error, LifecycleRuntime, Model, SignedInteger};
use packed_rmq::{native::NativeRuntime, RouteRuntime};

fn require(condition: bool) -> Result<(), String> {
    if condition { Ok(()) } else { Err("unexpected control result".into()) }
}

fn owner_errors() -> Result<(), Box<dyn std::error::Error>> {
    let runtime = LifecycleRuntime::new()?;
    require(matches!(SignedInteger::new(true, &[0]), Err(Error::Format)))?;
    require(matches!(SignedInteger::new(false, &[]), Err(Error::Format)))?;
    require(matches!(SignedInteger::new(false, &vec![0; 4097]), Err(Error::Limit)))?;
    require(matches!(runtime.profile(4097), Err(Error::Limit)))?;
    let profile = runtime.profile(2)?;
    let zero = profile.endpoint(&[0])?;
    let two = profile.endpoint(&[2])?;
    let one = profile.endpoint(&[1])?;
    let (mut owner, first) = {
        let input = [SignedInteger::new(true, &[2])?, SignedInteger::new(true, &[2])?];
        runtime.build_first(Model::Word, &input, &zero, &two, false)?
    };
    require(first.index_magnitude() == Some(vec![0]))?;
    drop(first);
    let before = owner.inspect()?;
    require(matches!(owner.query(&[], &two, false), Err(Error::Format)))?;
    require(owner.is_live())?;
    let after = owner.inspect()?;
    require(before.arrays.iter().zip(after.arrays).all(|(a, b)| a.identity == b.identity))?;
    let invalid = owner.query(&two, &one, false)?;
    require(invalid.answer.is_zero() && owner.is_live())?;
    drop(invalid);
    let valid = owner.query(&one, &two, false)?;
    require(valid.index_magnitude() == Some(vec![1]))?;
    drop(valid);
    let valid_again = owner.query(&zero, &two, false)?;
    require(valid_again.index_magnitude() == Some(vec![0]))?;
    drop(valid_again);
    drop(owner);

    let mut huge = vec![0; 251];
    huge[250] = 1; // -(2^2000) is outside the word profile for n=1.
    let input = [SignedInteger::new(true, &huge)?];
    let single = runtime.profile(1)?;
    let left = single.endpoint(&[0])?;
    let right = single.endpoint(&[1])?;
    require(matches!(runtime.build_first(Model::Word, &input, &left, &right, false), Err(Error::InputDomain)))?;
    let (owner, answer) = runtime.build_first(Model::Comparison, &input, &left, &right, false)?;
    require(answer.index_magnitude() == Some(vec![0]))?;
    drop(answer);
    drop(owner);
    Ok(())
}

fn poisoned_owner() -> Result<(), Box<dyn std::error::Error>> {
    let runtime = LifecycleRuntime::new()?;
    let profile = runtime.profile(1)?;
    let left = profile.endpoint(&[0])?;
    let right = profile.endpoint(&[1])?;
    let input = [SignedInteger::new(false, &[1])?];
    let (mut owner, first) = runtime.build_first(Model::Word, &input, &left, &right, false)?;
    require(first.index_magnitude() == Some(vec![0]))?;
    drop(first);
    std::env::set_var("PACKED_LIFECYCLE_FAIL_AFTER_TAKE", "1");
    // Admission rejection must happen before the armed transfer failure.
    let rejected = owner.query(&[], &right, false);
    let preserved = owner.is_live();
    let consumed = owner.query(&left, &right, false);
    std::env::remove_var("PACKED_LIFECYCLE_FAIL_AFTER_TAKE");
    require(matches!(rejected, Err(Error::Format)) && preserved)?;
    require(matches!(consumed, Err(Error::ControlledFailure)) && !owner.is_live())?;
    require(matches!(owner.inspect(), Err(Error::State)))?;
    require(matches!(owner.query(&left, &right, false), Err(Error::State)))?;
    drop(owner); // Empty-slot RAII drop must not free the consumed object again.
    Ok(())
}

fn execute(mode: &str) -> Result<(), Box<dyn std::error::Error>> {
    match mode {
        "owner-errors" => owner_errors(),
        "post-take-failure" => poisoned_owner(),
        "runtime-conflict-new-first" => {
            let _runtime = LifecycleRuntime::new()?;
            require(RouteRuntime::new().is_err())?;
            require(NativeRuntime::new().is_err())?;
            require(matches!(LifecycleRuntime::new(), Err(Error::RuntimeAlreadyClaimed)))?;
            Ok(())
        }
        "runtime-conflict-old-first" => {
            let _runtime = RouteRuntime::new()?;
            require(matches!(LifecycleRuntime::new(), Err(Error::RuntimeAlreadyClaimed)))?;
            Ok(())
        }
        "runtime-conflict-native-first" => {
            let _runtime = NativeRuntime::new()?;
            require(matches!(LifecycleRuntime::new(), Err(Error::RuntimeAlreadyClaimed)))?;
            Ok(())
        }
        "initialization-failure" => {
            std::env::set_var("PACKED_LIFECYCLE_FAIL_INIT", "1");
            require(matches!(LifecycleRuntime::new(), Err(Error::Initialization)))?;
            std::env::remove_var("PACKED_LIFECYCLE_FAIL_INIT");
            require(matches!(LifecycleRuntime::new(), Err(Error::RuntimeAlreadyClaimed)))?;
            require(RouteRuntime::new().is_err())?;
            require(NativeRuntime::new().is_err())?;
            Ok(())
        }
        _ => Err("unknown lifecycle Rust control".into()),
    }
}

fn main() {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    if arguments.len() != 1 {
        eprintln!("expected exactly one lifecycle Rust control");
        std::process::exit(2);
    }
    if let Err(error) = execute(&arguments[0]) {
        eprintln!("LIFE-NATIVE1 RUST {} FAIL {error}", arguments[0]);
        std::process::exit(1);
    }
    println!("LIFE-NATIVE1 RUST {} PASS", arguments[0]);
}
