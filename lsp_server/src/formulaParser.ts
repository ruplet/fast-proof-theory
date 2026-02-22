import { Formula } from "./types";

function isAlphaNum(ch: string | undefined): boolean {
  return !!ch && /[A-Za-z0-9_]/.test(ch);
}

export class FormulaParser {
  private pos = 0;

  constructor(private readonly input: string) {}

  parse(): Formula {
    const result = this.parseLolli();
    this.skipWs();
    if (this.pos !== this.input.length) {
      throw new Error(`Unexpected trailing input "${this.input.slice(this.pos)}"`);
    }
    return result;
  }

  private parseLolli(): Formula {
    const node = this.parseWith();
    if (this.matchSymbol("⊸") || this.matchSymbol("->") || this.matchWord("lolli")) {
      const right = this.parseLolli();
      return { node: "lolli", lolli: { left: node, right } };
    }
    return node;
  }

  private parseWith(): Formula {
    let node = this.parsePlus();
    while (true) {
      if (this.matchSymbol("&") || this.matchWord("with")) {
        const right = this.parsePlus();
        node = { node: "with", with: { left: node, right } };
        continue;
      }
      break;
    }
    return node;
  }

  private parsePlus(): Formula {
    let node = this.parseTensor();
    while (true) {
      if (this.matchSymbol("⊕") || this.matchSymbol("+") || this.matchWord("plus")) {
        const right = this.parseTensor();
        node = { node: "plus", plus: { left: node, right } };
        continue;
      }
      break;
    }
    return node;
  }

  private parseTensor(): Formula {
    let node = this.parseUnary();
    while (true) {
      if (
        this.matchSymbol("⊗") ||
        this.matchSymbol("*") ||
        this.matchWord("tensor") ||
        this.matchWord("times")
      ) {
        const right = this.parseUnary();
        node = { node: "tensor", tensor: { left: node, right } };
        continue;
      }
      break;
    }
    return node;
  }

  private parseUnary(): Formula {
    this.skipWs();
    if (this.matchSymbol("!") || this.matchWord("bang")) {
      const of = this.parseUnary();
      return { node: "bang", bang: { of } };
    }
    return this.parsePrimary();
  }

  private parsePrimary(): Formula {
    this.skipWs();
    if (this.matchSymbol("(")) {
      const inner = this.parseLolli();
      this.expectSymbol(")");
      return inner;
    }
    if (this.matchSymbol("1") || this.matchWord("one")) return { node: "one", one: {} };
    if (this.matchSymbol("⊤") || this.matchWord("top")) return { node: "top", top: {} };
    if (this.matchSymbol("0") || this.matchWord("zero")) return { node: "zero", zero: {} };

    const name = this.parseIdent();
    if (name) {
      const negated = this.matchSymbol("⊥");
      return { node: "atom", atom: { name, negated } };
    }

    if (this.matchSymbol("⊥") || this.matchWord("bot")) return { node: "bot", bot: {} };

    throw new Error("Expected a formula");
  }

  private parseIdent(): string | null {
    this.skipWs();
    const start = this.pos;
    while (isAlphaNum(this.peek())) this.pos++;
    if (this.pos > start) return this.input.slice(start, this.pos);
    return null;
  }

  private matchSymbol(sym: string): boolean {
    this.skipWs();
    if (this.input.startsWith(sym, this.pos)) {
      this.pos += sym.length;
      return true;
    }
    return false;
  }

  private matchWord(word: string): boolean {
    this.skipWs();
    if (this.input.startsWith(word, this.pos) && !isAlphaNum(this.input[this.pos + word.length])) {
      this.pos += word.length;
      return true;
    }
    return false;
  }

  private expectSymbol(sym: string) {
    if (!this.matchSymbol(sym)) {
      throw new Error(`Expected "${sym}"`);
    }
  }

  private skipWs() {
    while (/\s/.test(this.input[this.pos])) this.pos++;
  }

  private peek(): string | undefined {
    return this.input[this.pos];
  }
}

export function parseFormula(text: string): Formula {
  return new FormulaParser(text).parse();
}
