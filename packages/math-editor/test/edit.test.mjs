import { test } from "node:test";
import assert from "node:assert/strict";
import { MathEdit, read, write } from "../dist/index.js";

/** Type into a fresh editor (or one holding `src`). `{→}` `{←}` `{↑}` `{↓}` `{⌫}` `{del}` `{tab}`
 *  `{s-tab}` are keys; anything else is typed a character at a time. */
function typed(keys, src = "", known = []) {
  const r = src ? read(src, known) : { ok: true, stmt: { body: [] } };
  assert.ok(r.ok);
  const e = new MathEdit(r.stmt, { known });
  for (const k of keys.match(/\{[^}]+\}|[^{]/gu) ?? []) {
    switch (k) {
      case "{→}": e.right(); break;
      case "{←}": e.left(); break;
      case "{↑}": e.vertical(-1); break;
      case "{↓}": e.vertical(1); break;
      case "{⌫}": e.backspace(); break;
      case "{del}": e.deleteForward(); break;
      case "{tab}": if (!e.command()) e.hole(1); break;
      case "{s-tab}": e.hole(-1); break;
      case "{home}": e.home(); break;
      default: e.type(k);
    }
  }
  return { e, text: e.text, holes: write(e.stmt).holes };
}
const text = (keys, src, known) => typed(keys, src, known).text;

test("typing the raw syntax builds the structure and writes the same text", () => {
  for (const s of ["2x/3", "diff(x^2{→}, x)", "rref([1,2;3,4])", "(x+1)/(x-1)", "sqrt(2)", "sum(k^2{→}, k, 1, 10)",
    "integrate(cos(t)*sin(t), t, 0, 2pi)", "x y", "a*b/c", "-a/b", "sin(x)^2", "%2 + %"]) {
    const t = text(s);
    const want = s.replace(/\{→\}/g, "");
    assert.equal(read(t).ok && write(read(t).stmt).text, write(read(want).stmt).text, `${s} → ${t}`);
  }
  // an exponent keeps what is typed until → leaves it
  assert.equal(text("x^2+1"), "x^(2 + 1)");
  assert.equal(text("x^2{→}+1"), "x^2 + 1");
  // the numerator is what the engine would give it
  assert.equal(text("1+2x/3"), "1 + 2x/3");
  assert.equal(text("(a+b)/2"), "(a + b)/2");
  // a closed group that is the whole denominator or exponent ends it, as in the text, and its
  // parentheses go (the bar shows the grouping)
  assert.equal(text("(x+1)/(x-1)+1"), "(x + 1)/(x - 1) + 1");
  assert.equal(text("x^(2n)-1"), "x^(2n) - 1");
  assert.equal(typed("1/(x-1)").e.stmt.body[0].den.map((a) => a.k).join(" "), "ch ch ch");
  // a power of a fraction brings its parentheses
  assert.equal(text("1/2{→}^2"), "(1/2)^2");
  // `f(` is a call only once f is a function
  assert.deepEqual(typed("f(x").e.stmt.body.map((a) => a.k), ["ch", "paren"]);
  assert.deepEqual(typed("f(x", "", ["f"]).e.stmt.body.map((a) => a.k), ["call"]);
});

test("holes, Tab, and the backslash templates", () => {
  const d = typed("\\dint ");
  assert.equal(d.holes, 4);
  // a template starts in its first slot on screen and Tab follows the screen: ∫ from 0 to 1 of x² dx
  assert.equal(text("\\dint 0{tab}1{tab}x^2{→}{tab}x"), "integrate(x^2, x, 0, 1)");
  assert.equal(text("\\diff x{tab}x^2"), "diff(x^2, x)");
  // Tab wraps around to a hole behind the caret
  assert.equal(text("\\dint 0{→}{→}x{tab}t{tab}1"), "integrate(x, t, 0, 1)");
  assert.equal(text("\\frac 1{tab}2"), "1/2");
  assert.equal(text("\\mat2x3 "), "[, , ; , , ]");
  assert.equal(typed("\\mat2x3 ").holes, 6);
  assert.equal(text("\\vec3 1{tab}2{tab}3"), "[1; 2; 3]");
  assert.equal(text("\\sqrt 2"), "sqrt(2)");
  assert.equal(text("\\T M"), "transpose(M)");
  assert.equal(text("2\\pi r"), "2π r");
  assert.equal(text("\\pi +1"), "π + 1");
  assert.equal(text("\\alpha+\\beta "), "α + β");
  // an unknown command stays as typed
  assert.equal(text("\\nope "), "\\nope");
});

test("arrows walk the slots in the order they are on screen", () => {
  // d/dx (f): from the left, → enters the variable first, then the body
  const e = typed("", "diff(f, x)").e;
  e.home(); e.right();
  assert.equal(e.caret.block, e.stmt.body[0].args[1]);
  e.right(); e.right();
  assert.equal(e.caret.block, e.stmt.body[0].args[0]);
  // ↑ ↓ between a fraction's parts and a matrix's rows
  assert.equal(text("1/2{↑}0"), "10/2");
  assert.equal(text("[1,2;3,4{↑}9"), "[1, 29; 3, 4]");
  assert.equal(text("x^2{↓}+1"), "x^2 + 1");
});

test("backspace enters a structure from its end and removes it once empty", () => {
  assert.equal(text("1/2{→}{⌫}{⌫}{⌫}{⌫}{⌫}"), "");
  assert.equal(text("x^2{→}{⌫}{⌫}{⌫}"), "x");
  // at the start of a group or a one-argument call the wrapper goes and its contents stay
  assert.equal(text("(x+1{home}{→}{⌫}"), "x + 1");
  assert.equal(text("sqrt(x{home}{→}{⌫}"), "x");
  assert.equal(text("ab{⌫}"), "a");
  assert.equal(text("ab{home}{del}"), "b");
});
