// LIFE-1-R3 test double for .lake/build/bin/rmq_lifecycle_validate.exe, compiled
// only into disposable control copies. It emits the exact registry, startup and
// single-case surfaces that scripts/lifecycle_validator.ps1 checks, and applies
// the injected fault once during the single-case stage. LIFE-1-R4 adds
// block-durable: the validator's own RESULT.json path becomes a directory.
using System;
using System.IO;

public static class R3ValidatorDouble {
  static readonly string[] Ids = {"L01-W-EMPTY","L02-C-EMPTY","L03-W-SINGLE","L04-C-SINGLE",
    "L05-W-REPEAT","L06-C-REPEAT","L07-W-TIE","L08-C-TIE","L09-W-INVALID",
    "L10-C-INVALID","L11-W-DIRTY","L12-C-DIRTY","L13-W-N24","L14-C-N24",
    "L15-W-N83","L16-C-N83"};

  static bool Fault() {
    string mode = Environment.GetEnvironmentVariable("R3_FAULT_MODE");
    if (String.IsNullOrEmpty(mode) || mode == "intact") return false;
    string marker = Environment.GetEnvironmentVariable("R3_FAULT_MARKER");
    if (String.IsNullOrEmpty(marker) || File.Exists(marker)) return false;
    File.WriteAllText(marker, mode);
    string target = Environment.GetEnvironmentVariable("R3_FAULT_TARGET");
    if (mode == "change") { File.AppendAllText(target, "r3-injected-change"); return false; }
    if (mode == "change-fail") { File.AppendAllText(target, "r3-injected-change"); return true; }
    if (mode == "delete-fail") { File.Delete(target); return true; }
    if (mode == "fail") return true;
    if (mode == "block-durable") {
      string runs = Path.Combine(Environment.GetEnvironmentVariable("R3_FAULT_SCOPE"), ".lake", "lifecycle-validator");
      string[] dirs = Directory.GetDirectories(runs);
      if (dirs.Length != 1) throw new InvalidOperationException("R3-DOUBLE: validator log root is not unique");
      Directory.CreateDirectory(Path.Combine(dirs[0], "RESULT.json"));
      return false;
    }
    throw new InvalidOperationException("R3-DOUBLE: unsupported fault mode " + mode);
  }

  public static int Main(string[] args) {
    if (args.Length == 1 && args[0] == "--registry") {
      for (int i = 0; i < Ids.Length; i++) {
        string model = (i % 2 == 0) ? "word" : "comparison";
        string kind = (i >= 10 && i < 12) ? "dirty-entry" : "lifecycle";
        Console.WriteLine("LIFE1-REGISTRY|" + Ids[i] + "|" + model + "|" + kind + "|PASS");
      }
      return 0;
    }
    if (args.Length == 1 && args[0] == "--startup") {
      Console.WriteLine("LIFE1-STARTUP|PASS|cases=16");
      return 0;
    }
    if (args.Length == 1 && Array.IndexOf(Ids, args[0]) >= 0) {
      if (Fault()) {
        Console.Error.WriteLine("R3-DOUBLE: injected ordinary stage failure");
        return 1;
      }
      Console.WriteLine("LIFE1-CASE|" + args[0] + "|PASS|steps=1|queries=1|querySteps=1|extent=1|peak=1|release=1|dirty=0");
      Console.WriteLine("LIFE1-PASS|mode=single|cases=1");
      return 0;
    }
    Console.Error.WriteLine("LIFE1-FAIL|r3-double-unsupported");
    return 2;
  }
}
