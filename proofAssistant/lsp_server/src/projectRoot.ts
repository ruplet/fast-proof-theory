import * as fs from "fs";
import * as path from "path";

const MARKERS = ["prover-toolchain", "proverfile.toml", "proverfile.lean"];
const IGNORED_SEGMENTS = new Set([".prover", "packages", "build", "out"]);

function hasIgnoredSegment(p: string): boolean {
  return p.split(path.sep).some((segment) => IGNORED_SEGMENTS.has(segment));
}

export function findProjectRoot(startDir: string): string {
  let current = path.resolve(startDir);
  while (true) {
    if (!hasIgnoredSegment(current)) {
      for (const marker of MARKERS) {
        if (fs.existsSync(path.join(current, marker))) {
          return current;
        }
      }
    }

    const parent = path.dirname(current);
    if (parent === current) break;
    current = parent;
  }
  return path.resolve(startDir);
}
