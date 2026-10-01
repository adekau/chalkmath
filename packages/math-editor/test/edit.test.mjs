import { test } from "node:test";
import assert from "node:assert/strict";
import { MathEdit, read, write, templateInText, toLatex } from "../dist/index.js";

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
      case "{end}": e.end(); break;
      case "{undo}": e.undo(); break;
      case "{redo}": e.redo(); break;
      case "{s-←}": e.extend(); e.left(); break;
      case "{s-→}": e.extend(); e.right(); break;
      case "{all}": e.selectAll(); break;
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

test("undo takes back a run of typing, a structure, or a deletion as one step; redo puts it back", () => {
  assert.equal(text("x+1{undo}"), "x + ");
  assert.equal(text("abc{undo}"), "");
  assert.equal(text("ab{←}c{undo}"), "ab");   // a move ends the run
  assert.equal(text("1/2{undo}"), "1/()");
  // undoing a template goes back to the command as typed, like undoing an autocorrection
  assert.equal(text("\\sqrt x{undo}{undo}"), "\\sqrt");
  assert.equal(text("\\sqrt x{undo}{undo}{redo}"), "sqrt()");
  assert.equal(text("abc{⌫}{⌫}{undo}"), "abc");
  assert.equal(text("x{undo}{redo}{redo}"), "x");
  // after undo, the caret is back where it was and typing carries on from there
  assert.equal(text("x^2{undo}3"), "x^3");
  // a new edit after undo drops what redo would have put back
  assert.equal(text("ab{undo}c{redo}"), "c");
});

test("a selection is whole atoms of one block, and edits act on it", () => {
  const sel = (keys, src) => { const { e } = typed(keys, src); const s = e.selection(); return s && e.selectedText(); };
  assert.equal(sel("{end}{s-←}{s-←}", "x + 12"), "12");
  // reaching into a fraction selects all of it
  assert.equal(sel("{end}{s-←}{s-←}", "1 + a/b"), "a/b");
  assert.equal(sel("{all}", "diff(x^2, x)"), "diff(x^2, x)");
  assert.equal(text("{end}{s-←}{s-←}{⌫}", "x + 12"), "x + ");
  assert.equal(text("{end}{s-←}{s-←}9", "x + 12"), "x + 9");
  assert.equal(text("{end}{s-←}{s-←}9{undo}", "x + 12"), "x + 12");
  // / makes the selection a numerator, ( puts it in parentheses
  assert.equal(text("{all}/2", "x + 1"), "(x + 1)/2");
  assert.equal(text("{all}(", "x + 1"), "(x + 1)");
  // ← and → on a selection go to its ends
  const { e } = typed("{end}{s-←}{s-←}", "x + 12");
  e.collapse(-1); e.type("-");
  assert.equal(e.text, "x + -12");
});

test("paste reads the text as structure where it can", () => {
  const pasted = (src, clip, keys = "") => { const { e } = typed(keys, src); e.paste(clip); return e; };
  let e = pasted("", "1/2 + diff(x^2, x)");
  assert.deepEqual(e.stmt.body.map((a) => a.k), ["frac", "ch", "call"]);
  assert.equal(e.text, "1/2 + diff(x^2, x)");
  // at the caret, inside a slot
  e = pasted("", "x^2", "\\sqrt ");
  assert.equal(e.text, "sqrt(x^2)");
  // a whole `let` into an empty input is the cell's head too
  e = pasted("", "let f(x) = x^2");
  assert.equal(e.text, "let f(x) = x^2");
  // text that is not an expression is typed as far as it goes: `⟦`, `{` mean nothing here
  e = pasted("", "a+⟦b⟧");
  assert.equal(e.text, "a + b");
  // one step to undo
  e = pasted("", "1/2 + 3");
  e.undo();
  assert.equal(e.text, "");
});

test("a let head is typed as it reads, and its name and parameters are slots", () => {
  assert.equal(text("let f(x, y) = x*y"), "let f(x, y) = x*y");
  assert.equal(text("let a = 2"), "let a = 2");
  assert.equal(typed("let ").holes, 2);                 // the name, and the body
  // Tab goes name → body; a parameter list can grow and shrink
  assert.equal(text("let g{tab}x^2", ""), "let g = x^2");
  assert.equal(text("let f(x,{⌫}{⌫}{⌫}{tab}x", ""), "let f = x");
  // the function's own body may call it
  const { e } = typed("let f(n) = f(n");
  assert.equal(e.stmt.body[1].k, "call");
  // a numerator stops at the head, and a minus after it is a negation
  assert.equal(text("let h = x/2"), "let h = x/2");
  assert.equal(text("let h = -x"), "let h = -x");
  // the caret walks through the head like any slot
  const t = typed("", "let f(x) = x");
  t.e.home(); t.e.right(); assert.equal(t.e.caret.block, t.e.stmt.body[0].name);
});

test("the call around the caret, for signature help, is one drawn as name(args)", () => {
  const ctx = (keys, src, known) => typed(keys, src, known).e.callContext();
  assert.deepEqual(ctx("subst(x^2{→}, x, 3"), { name: "subst", arg: 2, firstArg: "x^2" });
  assert.deepEqual(ctx("rref([1,2;3,4"), { name: "rref", arg: 0, firstArg: "[1, 2; 3, 4]" });
  // inside √ inside N: the √ shows its slot already, so it is N's first argument
  assert.deepEqual(ctx("N(sqrt(2"), { name: "N", arg: 0, firstArg: "sqrt(2)" });
  assert.equal(ctx("diff(x^2"), null);
  assert.deepEqual(ctx("f(1, 2", "", ["f"]), { name: "f", arg: 1, firstArg: "1" });
});

test("a template typed in a cell's text lands where it was typed, in a tree", () => {
  const at = (before, after = "") => { const e = templateInText(before, after); return e && [e.text, e.caret.block.length === 0]; };
  assert.deepEqual(at("\\frac"), ["()/()", true]);
  assert.deepEqual(at("1 + \\frac"), ["1 + ()/()", true]);
  assert.deepEqual(at("rref(\\mat2x2", ")"), ["rref([, ; , ])", true]);
  assert.deepEqual(at("x \\sqrt", " + 1"), ["x sqrt() + 1", true]);
  assert.deepEqual(at("x^2 + \\int"), ["x^2 + integrate(, )", true]);
  // the rest of the text keeps its reading: x^2 + 1 is not typed into the exponent
  assert.equal(templateInText("x^2 + 1 + \\sqrt", "").text, "x^2 + 1 + sqrt()");
  // not a template, or text that does not read around it: nothing
  assert.equal(templateInText("\\pi", ""), null);
  assert.equal(templateInText("rref(\\frac", ""), null);
  // the template is one step to undo
  const e = templateInText("1 + \\frac", "");
  e.undo();
  assert.equal(e.text, "1 + ");
});

test("a ( typed before existing atoms takes them in, with its ) open until one is typed", () => {
  // the case from the notebook: wrap a product in expand( after the fact
  let t = typed("{home}expand(", "(x + 5)(2x + 3)");
  assert.equal(t.text, "expand((x + 5)(2x + 3))");
  assert.equal(t.e.stmt.body[0].open, true);
  assert.equal(t.e.caret.block, t.e.stmt.body[0].args[0]);
  // End then ) places the ) where it already is
  t = typed("{home}expand({end})", "(x + 5)(2x + 3)");
  assert.equal(t.text, "expand((x + 5)(2x + 3))");
  assert.equal(t.e.stmt.body[0].open, undefined);
  // a ) typed inside puts what follows back out, as in the text
  assert.equal(text("{home}expand({→}{→}{→}{→}{→})", "(x + 5)(2x + 3)"), "expand((x + 5))(2x + 3)");
  // a plain group too: 2( in front of x + 1
  assert.equal(text("{home}{→}(", "2x + 1"), "2(x + 1)");
  assert.equal(text("{home}{→}({→}{→}{→})", "2x + 1"), "2(x + 1)");
  assert.equal(text("{home}{→}({→})", "2x + 1"), "2(x) + 1");
  // typed at the end, a ( closes as before
  assert.equal(typed("sin(x").e.stmt.body[0].open, undefined);
});

test("backspace after a ) opens the group again; at a ( only the ( goes", () => {
  // the ) goes: sin(x) + 1 → sin(x + 1), nothing deleted
  let t = typed("{end}{←}{←}{⌫}", "sin(x) + 1");
  assert.equal(t.text, "sin(x + 1)");
  assert.equal(t.e.stmt.body[0].open, true);
  // and typing ) puts it back where it was
  assert.equal(text("{end}{←}{←}{⌫})", "sin(x) + 1"), "sin(x) + 1");
  // after an open group, backspace steps in rather than deleting it
  assert.equal(text("{home}expand({end}{⌫}", "(x + 5)(2x + 3)"), "expand((x + 5)(2x + 3))");
  // at the start of a call drawn as name(…), the ( goes and the name stays
  assert.equal(text("{home}expand({⌫}", "(x + 5)"), "expand(x + 5)");
  assert.deepEqual(typed("{home}expand({⌫}", "(x + 5)").e.stmt.body.map((a) => a.k).join(" "), "ch ch ch ch ch ch paren");
  // and an empty call's ( leaves its name to go on typing
  assert.equal(text("f({⌫}", "", ["f"]), "f");
  // a notated call (√) leaves its contents, as before
  assert.equal(text("sqrt(x{home}{→}{⌫}"), "x");
});

test("a comma in the middle of an argument starts the next one with what follows", () => {
  assert.equal(text("f(ab{←},", "", ["f"]), "f(a, b)");
  assert.equal(text("{home}{→}{→},", "subst(ab, x, 1)"), "subst(a, b, x, 1)");
});

test("leaving the input places every open )", () => {
  const { e } = typed("{home}expand(", "(x + 5)(2x + 3)");
  e.closeAll();
  assert.equal(e.stmt.body[0].open, undefined);
});

test("backspace at the start of an empty column, row or argument takes its `,` or `;`", () => {
  // [1, ⌫ ; → a 2×1 matrix, not 2×2
  const { e } = typed("[1,{⌫};2");
  assert.equal(e.text, "[1; 2]");
  assert.equal(text("[1,2;{⌫}"), "[1, 2]");
  // a column with something in it stays; the caret only moves back
  assert.equal(text("[1,2;3,{⌫}4"), "[1, 2; 34, ]");
  assert.equal(text("f(a,{⌫}", "", ["f"]), "f(a)");
});

test("a function's name typed in front of a group becomes its call once the caret leaves the name", () => {
  const { e } = typed("(v+1){home}norm");
  // still at the end of the name: it may yet grow (`N` into `norm`)
  assert.deepEqual(e.stmt.body.map((a) => a.k), ["ch", "ch", "ch", "ch", "paren"]);
  e.right(); e.settle();
  assert.deepEqual(e.stmt.body.map((a) => a.k), ["call"]);
  assert.equal(e.stmt.body[0].name, "norm");
  assert.equal(e.text, "norm(v + 1)");
  // the caret went into the parentheses, and stays at the start of the argument
  assert.equal(e.caret.block, e.stmt.body[0].args[0]);
  assert.equal(e.caret.i, 0);
  // leaving the input settles it wherever the caret is
  const t = typed("(x-1){home}abs").e;
  t.settle(true);
  assert.equal(t.stmt.body[0].name, "abs");
  // a name that is not a function stays a product, as the text reads it
  const x = typed("(a+b){home}x").e;
  x.settle(true);
  assert.deepEqual(x.stmt.body.map((a) => a.k), ["ch", "paren"]);
});

test("@ puts the selection in parentheses with a box in front for a function's name", () => {
  // select all, @, type the name, → into the group: the call
  const { e } = typed("x/2{→}+1{all}@norm");
  assert.equal(e.text, "norm(x/2 + 1)");
  assert.deepEqual(e.stmt.body.map((a) => a.k), ["ch", "ch", "ch", "ch", "paren"]);
  assert.match(toLatex(e.stmt), /norm/);
  e.right(); e.settle();
  assert.deepEqual(e.stmt.body.map((a) => a.k), ["call"]);
  assert.equal(e.stmt.body[0].args[0], e.caret.block);
  // the box shows until a name is typed there
  const box = typed("a+b{all}@").e;
  assert.match(toLatex(box.stmt), /\\htmlData\{fh=1\}/);
  assert.equal(box.text, "(a + b)");
  // backspace in the empty box undoes the @; after a name, it takes the name first
  assert.equal(text("a+b{all}@{⌫}"), "a + b");
  const back = typed("a+b{all}@ab{⌫}{⌫}{⌫}").e;
  assert.equal(back.text, "a + b");
  assert.deepEqual(back.stmt.body.map((a) => a.k), ["ch", "ch", "ch"]);
  // left unnamed, the group is just parentheses once the caret goes elsewhere
  const left = typed("a+b{all}@{→}").e;
  left.settle();
  assert.equal(left.stmt.body[0].head, undefined);
  assert.equal(left.text, "(a + b)");
});

/** Type characters one at a time (braces and all, which `typed` would read as keys). */
function typeChars(e, s) { for (const c of s) e.type(c); return e; }

test("[[ after a value opens a part; its indices are typed as written", () => {
  const e = typeChars(new MathEdit({ body: [] }), 'planets[[All, "mass"]]');
  assert.equal(e.text, 'planets[[All, "mass"]]');
  assert.equal(typeChars(new MathEdit({ body: [] }), 'mean(t[["a b, c", 2;;-1]])').text, 'mean(t[["a b, c", 2;;-1]])');
  assert.equal(typeChars(new MathEdit({ body: [] }), "m[[{1, 3}, -1]]^2").text, "m[[{1,3}, -1]]^2");
  // not after a value: a matrix, as before; a space keeps the product
  assert.equal(typeChars(new MathEdit({ body: [] }), "[[1]]").text, "[[1]]");
  assert.equal(typeChars(new MathEdit({ body: [] }), "x [1, 2]").text, "x [1, 2]");
  assert.match(toLatex(read('t[[All, "ma"]]').stmt), /\\llbracket .*\\mathrm\{All\}.*\\text\{“\}.*\\rrbracket/);
});

test("what completions need: the name being typed, and the part index at the caret", () => {
  const e = typeChars(new MathEdit({ body: [] }), "2+vari");
  assert.deepEqual(e.nameBefore(), { name: "vari", start: 2 });
  assert.ok(e.completeName("variance"));
  typeChars(e, "[1, 3]");
  assert.equal(e.text, "2 + variance([1, 3])");
  const p = typeChars(new MathEdit({ body: [] }), 'mean(t[[All, "ma');
  assert.deepEqual(p.partBefore(), { text: 'mean(t[[All, "ma', typed: "ma", start: 0, quoted: true });
  assert.equal(p.nameBefore(), null);   // in an index, names are the part's, not functions
  assert.ok(p.completeIndex('"mass"'));
  assert.equal(p.text, 'mean(t[[All, "mass"]])');
});
