// LIFE-1-R4 test double for git.exe, compiled only into a directory that the
// failure-control runner prepends to PATH for one disposable control launch.
// Until the control's fault marker exists it forwards the exact command line to
// the real git (R3_REAL_GIT) with inherited standard handles and returns its
// exit code. Once the marker exists (the injected stage or capture override
// writes it), mode git-hang sleeps past any finalization deadline and mode
// git-fail writes one stderr line and exits 128.
using System;
using System.Diagnostics;
using System.IO;
using System.Threading;

public static class R4GitDouble {
  static string ArgumentsAfterProgram(string commandLine) {
    string s = commandLine.TrimStart();
    int end;
    if (s.StartsWith("\"")) {
      end = s.IndexOf('"', 1);
      end = end < 0 ? s.Length : end + 1;
    } else {
      end = s.IndexOf(' ');
      if (end < 0) end = s.Length;
    }
    return s.Substring(end).TrimStart();
  }

  public static int Main(string[] args) {
    string mode = Environment.GetEnvironmentVariable("R3_FAULT_MODE");
    string marker = Environment.GetEnvironmentVariable("R3_FAULT_MARKER");
    bool armed = !String.IsNullOrEmpty(marker) && File.Exists(marker);
    if (armed && mode == "git-hang") {
      Thread.Sleep(600000);
      return 124;
    }
    if (armed && mode == "git-fail") {
      Console.Error.WriteLine("R3-DOUBLE: injected git failure");
      return 128;
    }
    string real = Environment.GetEnvironmentVariable("R3_REAL_GIT");
    if (String.IsNullOrEmpty(real) || !File.Exists(real)) {
      Console.Error.WriteLine("R3-DOUBLE: real git unavailable");
      return 127;
    }
    ProcessStartInfo start = new ProcessStartInfo(real, ArgumentsAfterProgram(Environment.CommandLine));
    start.UseShellExecute = false;
    using (Process p = Process.Start(start)) {
      p.WaitForExit();
      return p.ExitCode;
    }
  }
}
