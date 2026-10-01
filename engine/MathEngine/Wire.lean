import MathEngine.Expr
import MathEngine.Json
import MathEngine.Rewrite
import MathEngine.Print
/-! # Wire format — must match `WireExpr` in `packages/protocol/src/index.ts`. -/
namespace MathEngine

partial def Expr.toJson : Expr → Json
  | .num q => .obj #[("k", .str "num"), ("v", .obj #[("num", .str (toString q.val.num)), ("den", .str (toString q.val.den))])]
  | .var x => .obj #[("k", .str "var"), ("name", .str x)]
  | .add es => .obj #[("k", .str "add"), ("args", .arr (es.toArray.map toJson))]
  | .mul es => .obj #[("k", .str "mul"), ("args", .arr (es.toArray.map toJson))]
  | .pow b e => .obj #[("k", .str "pow"), ("base", toJson b), ("exp", toJson e)]
  | .fn f es => .obj #[("k", .str "fn"), ("name", .str f), ("args", .arr (es.toArray.map toJson))]
  | .matrix rs => .obj #[("k", .str "matrix"), ("rows", .arr (rs.toArray.map fun r => .arr (r.toArray.map toJson)))]

def Path.toJson (p : Path) : Json := .arr (p.toArray.map fun i => .num (toString i))

mutual
  /-- `paths` annotates the rendered term with subterm paths, so a page can make it selectable. -/
  partial def Step.toJson (s : Step) (paths : Bool := false) : Json :=
    let base := #[("rule", .str s.rule), ("explanation", .str s.explanation), ("path", Path.toJson s.path),
                  ("before", s.before.toJson), ("after", s.after.toJson),
                  -- optional per protocol rule 5: the whole term after the step, rendered; and before it, since the
                  -- pipeline canonicalizes silently between steps, so `before` need not be the previous `after`
                  ("beforeRendered", .obj #[("text", .str s.before.toText), ("latex", .str (s.before.toLatex paths))]),
                  ("afterRendered", .obj #[("text", .str s.after.toText), ("latex", .str (s.after.toLatex paths))])]
    .obj (match s.sub with | some d => base.push ("sub", d.toJson paths) | none => base)
  partial def Derivation.toJson (d : Derivation) (paths : Bool := false) : Json :=
    .obj #[("input", d.input.toJson), ("steps", .arr (d.steps.map fun s => Step.toJson s paths)), ("output", d.output.toJson),
           -- the input rendered too, so a nested derivation's first step has a "before" to show
           ("inputRendered", .obj #[("text", .str d.input.toText), ("latex", .str (d.input.toLatex paths))])]
  /-- A step without its terms: what `outline` replies carry (the rule, why, where, and whether the
  term prints the same before and after, which a frontend folds), so that a derivation of a big term
  costs what its steps say rather than what its terms weigh. `engine.steps` sends the terms. -/
  partial def Step.outlineJson (s : Step) : Json :=
    let base := #[("rule", .str s.rule), ("explanation", .str s.explanation), ("path", Path.toJson s.path)]
    let base := if s.sub.isNone && s.before.toLatex false == s.after.toLatex false then base.push ("quiet", .bool true) else base
    .obj (match s.sub with | some d => base.push ("sub", d.outlineJson) | none => base)
  partial def Derivation.outlineJson (d : Derivation) : Json :=
    .obj #[("steps", .arr (d.steps.map Step.outlineJson))]
end

end MathEngine
