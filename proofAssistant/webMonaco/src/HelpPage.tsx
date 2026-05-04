import { DomainInfo } from "../../protocol/types";

type Props = {
  info: DomainInfo;
};

const RULES_BY_SYSTEM: Record<string, Record<string, string[]>> = {
  CLLp: {
    ax: ["Γ, φ ⊢ φ, Δ", "──────────── (AX)"],
    rlolli: ["Γ, φ ⊢ ψ, Δ", "────────────── (R⊸)", "Γ ⊢ φ ⊸ ψ, Δ"],
    rwith: ["Γ ⊢ φ, Δ    Γ ⊢ ψ, Δ", "────────────────── (R&)", "Γ ⊢ φ & ψ, Δ"],
    rplusl: ["Γ ⊢ φ, Δ", "────────── (R⊕L)", "Γ ⊢ φ ⊕ ψ, Δ"],
    rplusr: ["Γ ⊢ ψ, Δ", "────────── (R⊕R)", "Γ ⊢ φ ⊕ ψ, Δ"],
    rtensor: ["Γ ⊢ φ, Δ    Σ ⊢ ψ, Π", "────────────────────── (R⊗)", "Γ, Σ ⊢ φ ⊗ ψ, Δ, Π"],
    rpar: ["Γ ⊢ φ, ψ, Δ", "──────────── (R⅋)", "Γ ⊢ φ ⅋ ψ, Δ"],
    rbot: ["Γ ⊢ Δ", "──────── (Rbot)", "Γ ⊢ bot, Δ"],
    lwithl: ["Γ, φ, Δ ⊢ Σ", "──────────── (L&L)", "Γ, φ & ψ, Δ ⊢ Σ"],
    lwithr: ["Γ, ψ, Δ ⊢ Σ", "──────────── (L&R)", "Γ, φ & ψ, Δ ⊢ Σ"],
    ltensor: ["Γ, φ, ψ, Δ ⊢ Σ", "────────────── (L⊗)", "Γ, φ ⊗ ψ, Δ ⊢ Σ"],
    lplus: ["Γ, φ, Δ ⊢ Σ    Γ, ψ, Δ ⊢ Σ", "──────────────────────── (L⊕)", "Γ, φ ⊕ ψ, Δ ⊢ Σ"],
    lbang: ["Γ, φ, Δ ⊢ Σ", "────────── (L!)", "Γ, !φ, Δ ⊢ Σ"],
    rbang: ["!Γ ⊢ φ, Δ", "────────── (R!)", "!Γ ⊢ !φ, Δ"],
    contractbang: ["Γ, !φ, !φ, Δ ⊢ Σ", "─────────────── (LC!)", "Γ, !φ, Δ ⊢ Σ"],
  },
  ILLp: {
    ax: ["Γ, φ ⊢ φ", "────────── (AX)"],
    rlolli: ["Γ, φ ⊢ ψ", "────────── (R⊸)", "Γ ⊢ φ ⊸ ψ"],
    rwith: ["Γ ⊢ φ    Γ ⊢ ψ", "──────────── (R&)", "Γ ⊢ φ & ψ"],
    rplusl: ["Γ ⊢ φ", "──────── (R⊕L)", "Γ ⊢ φ ⊕ ψ"],
    rplusr: ["Γ ⊢ ψ", "──────── (R⊕R)", "Γ ⊢ φ ⊕ ψ"],
    rtensor: ["Γ ⊢ φ    Σ ⊢ ψ", "────────────── (R⊗)", "Γ, Σ ⊢ φ ⊗ ψ"],
    lwithl: ["Γ, φ, Δ ⊢ Σ", "──────────── (L&L)", "Γ, φ & ψ, Δ ⊢ Σ"],
    lwithr: ["Γ, ψ, Δ ⊢ Σ", "──────────── (L&R)", "Γ, φ & ψ, Δ ⊢ Σ"],
    ltensor: ["Γ, φ, ψ, Δ ⊢ Σ", "────────────── (L⊗)", "Γ, φ ⊗ ψ, Δ ⊢ Σ"],
    lplus: ["Γ, φ, Δ ⊢ Σ    Γ, ψ, Δ ⊢ Σ", "──────────────────────── (L⊕)", "Γ, φ ⊕ ψ, Δ ⊢ Σ"],
    lbang: ["Γ, φ, Δ ⊢ Σ", "────────── (L!)", "Γ, !φ, Δ ⊢ Σ"],
    rbang: ["!Γ ⊢ φ", "──────── (R!)", "!Γ ⊢ !φ"],
    contractbang: ["Γ, !φ, !φ, Δ ⊢ Σ", "─────────────── (LC!)", "Γ, !φ, Δ ⊢ Σ"],
  },
};

const tutorial = `theorem demo using CLLp : (A ⊸ A) := by
  rlolli h
  ax h`;

const theoremStarters = [
  "theorem <name> using CLLp : <formula> := by",
  "theorem <name> using ILLp : <formula> := by",
];

const shortcuts = [
  { shortcut: "\\tensor", output: "⊗", meaning: "Tensor / multiplicative conjunction" },
  { shortcut: "\\par", output: "⅋", meaning: "Par / multiplicative disjunction" },
  { shortcut: "\\oplus", output: "⊕", meaning: "Plus / additive disjunction" },
  { shortcut: "\\with", output: "&", meaning: "With / additive conjunction" },
  { shortcut: "\\lolli", output: "⊸", meaning: "Linear implication" },
  { shortcut: "\\^bot", output: "^bot", meaning: "Postfix classical linear negation" },
];

export function HelpPage({ info }: Props) {
  return (
    <div style={{ height: "100%", overflow: "auto", padding: 20, fontFamily: "ui-sans-serif, system-ui, sans-serif" }}>
      <h1 style={{ marginTop: 0 }}>MyPA Help</h1>

      <h2>Quick Start</h2>
      <p>Start with one of these theorem headers, then list one tactic per line below <code>:= by</code>.</p>
      <ul>
        {theoremStarters.map((starter) => (
          <li key={starter}><code>{starter}</code></li>
        ))}
      </ul>
      <pre style={{ background: "#f6f8fa", padding: 12, border: "1px solid #d0d7de", borderRadius: 6, overflowX: "auto" }}>{tutorial}</pre>

      <h2>Syntax</h2>
      <ul>
        <li><code>theorem &lt;name&gt; using &lt;logic&gt; : &lt;formula&gt; := by</code></li>
        <li>Currently supported linear theorem systems are <code>CLLp</code> and <code>ILLp</code>.</li>
        <li>Classical linear negation is written as postfix <code>A^bot</code>; type <code>A\^bot</code> to use the shortcut.</li>
        <li>One tactic per line below the header.</li>
        <li>Line comments start with <code>--</code>.</li>
      </ul>

      <h2>Symbol Shortcuts</h2>
      <p>Type a backslash prefix such as <code>\lol</code> or <code>\ten</code> to open symbol suggestions. Selecting a suggestion inserts the symbol, and typing a full shortcut such as <code>\lolli</code> converts it in place.</p>
      <table style={{ width: "100%", borderCollapse: "collapse", marginBottom: 24 }}>
        <thead>
          <tr>
            <th style={{ textAlign: "left", borderBottom: "1px solid #d0d7de", padding: "6px 4px", width: "20%" }}>Shortcut</th>
            <th style={{ textAlign: "left", borderBottom: "1px solid #d0d7de", padding: "6px 4px", width: "15%" }}>Output</th>
            <th style={{ textAlign: "left", borderBottom: "1px solid #d0d7de", padding: "6px 4px" }}>Meaning</th>
          </tr>
        </thead>
        <tbody>
          {shortcuts.map((item) => (
            <tr key={item.shortcut}>
              <td style={{ borderBottom: "1px solid #eaeef2", padding: "8px 4px" }}><code>{item.shortcut}</code></td>
              <td style={{ borderBottom: "1px solid #eaeef2", padding: "8px 4px" }}><code>{item.output}</code></td>
              <td style={{ borderBottom: "1px solid #eaeef2", padding: "8px 4px" }}>{item.meaning}</td>
            </tr>
          ))}
        </tbody>
      </table>

      <h2>Systems</h2>
      {info.systems.map((system) => (
        <section key={system.key} style={{ marginBottom: 24 }}>
          <h3 style={{ marginBottom: 6 }}>{system.key}</h3>
          <div style={{ marginBottom: 8 }}>{system.title}</div>
          <div style={{ marginBottom: 8, color: "#57606a" }}>{system.summary}</div>
          <div style={{ marginBottom: 10 }}>Aliases: {system.aliases.join(", ") || "none"}</div>
          <table style={{ width: "100%", borderCollapse: "collapse", tableLayout: "fixed" }}>
            <thead>
              <tr>
                <th style={{ textAlign: "left", borderBottom: "1px solid #d0d7de", padding: "6px 4px", width: "20%" }}>Tactic</th>
                <th style={{ textAlign: "left", borderBottom: "1px solid #d0d7de", padding: "6px 4px", width: "30%" }}>Usage</th>
                <th style={{ textAlign: "left", borderBottom: "1px solid #d0d7de", padding: "6px 4px" }}>Rule</th>
              </tr>
            </thead>
            <tbody>
              {system.tactics.map((tactic) => (
                <tr key={`${system.key}:${tactic.name}`}>
                  <td style={{ borderBottom: "1px solid #eaeef2", padding: "8px 4px", verticalAlign: "top" }}>
                    <code>{tactic.name}</code>
                  </td>
                  <td style={{ borderBottom: "1px solid #eaeef2", padding: "8px 4px", verticalAlign: "top" }}>
                    <code>{tactic.display}</code>
                  </td>
                  <td style={{ borderBottom: "1px solid #eaeef2", padding: "8px 4px", verticalAlign: "top" }}>
                    <div style={{ marginBottom: 6 }}>{tactic.summary}</div>
                    <pre style={{ margin: 0, background: "#f6f8fa", border: "1px solid #eaeef2", borderRadius: 6, padding: 8, overflowX: "auto" }}>
                      {(RULES_BY_SYSTEM[system.key] && RULES_BY_SYSTEM[system.key][tactic.name]
                        ? RULES_BY_SYSTEM[system.key][tactic.name]
                        : ["Rule documentation not available."]).join("\n")}
                    </pre>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </section>
      ))}
    </div>
  );
}
