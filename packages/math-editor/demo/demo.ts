// The visual input on its own page: type, click, and watch the source text it writes.
import "katex/dist/katex.min.css";
import { MathInput } from "../src/view.js";

const samples = ["diff(x^2*sin(x), x)", "integrate(cos(t)*sin(t), t, 0, 2pi)", "sum(k^2, k, 1, 10)", "(x + 1)/(x - 1) + sqrt(2)",
  "det([a, b; c, d])", "rref([1, 2, 3; 4, 5, 6; 7, 8, 10])", "x^(1/2) + abs(3 + 4i)", "let f(x, y) = x^2 + y", ""];
const host = document.querySelector("#inputs")!;
const inputs: MathInput[] = [];
for (const src of samples) {
  const row = document.createElement("div");
  row.className = "row";
  const out = document.createElement("code");
  const mi = MathInput.fromSource(src, { label: "Demo input", onChange: (t, holes) => { out.textContent = t + (holes ? `   (${holes} empty)` : ""); } })!;
  out.textContent = src;
  inputs.push(mi);
  row.append(mi.el, out);
  host.append(row);
}
Object.assign(window, { ready: true, inputs });
