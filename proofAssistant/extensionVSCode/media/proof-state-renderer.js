(function () {
  function esc(s) {
    return String(s).replace(/[&<>"']/g, function (c) {
      return {
        "&": "&amp;",
        "<": "&lt;",
        ">": "&gt;",
        '"': "&quot;",
        "'": "&#39;",
      }[c];
    });
  }

  function renderFormulaHtml(input) {
    var text = String(input ?? "");
    var depth = 0;
    var out = "";
    var operatorChars = new Set(["⊗", "⊕", "⊸", "&", "⅋", "!", "?", "⊤", "⊥"]);
    for (var i = 0; i < text.length; i += 1) {
      var ch = text[i];
      if (ch === "(") {
        var openClass = "paren-" + (depth % 6);
        out += "<span class='" + openClass + "'>(</span>";
        depth += 1;
        continue;
      }
      if (ch === ")") {
        depth = Math.max(depth - 1, 0);
        var closeClass = "paren-" + (depth % 6);
        out += "<span class='" + closeClass + "'>)</span>";
        continue;
      }
      if (operatorChars.has(ch)) {
        out += "<span class='op'>" + esc(ch) + "</span>";
        continue;
      }
      out += esc(ch);
    }
    return "<span class='formula'>" + out + "</span>";
  }

  function clear(root, meta) {
    if (meta) {
      meta.textContent = "";
    }
    root.className = "empty";
    root.innerHTML = "No proof state.";
  }

  function render(root, meta, state) {
    var goals = state && Array.isArray(state.goals) ? state.goals : [];
    var display = state && state.display ? state.display : null;
    var tone = state && state.tone ? state.tone : "normal";
    var sections = display && Array.isArray(display.sections) ? display.sections : [];
    var rulesSection = sections.find(function (section) { return section.title === "Rules"; });
    var profileSection = sections.find(function (section) { return section.title === "Profile"; });
    var calculusSection = sections.find(function (section) { return section.title === "Calculus"; });
    var logicLabel = rulesSection && Array.isArray(rulesSection.body) && rulesSection.body.length
      ? String(rulesSection.body[0])
      : profileSection && Array.isArray(profileSection.body) && profileSection.body.length
      ? String(profileSection.body[0])
      : "";
    var calculusLabel = calculusSection && Array.isArray(calculusSection.body) && calculusSection.body.length
      ? String(calculusSection.body[0])
      : "";
    var isSequent = /sequent|gentzen/i.test(calculusLabel);
    var countLabel = goals.length
      ? goals.length + " " + (isSequent ? (goals.length === 1 ? "sequent" : "sequents") : (goals.length === 1 ? "goal" : "goals"))
      : "";
    if (meta) {
      meta.textContent = [countLabel, calculusLabel || logicLabel].filter(Boolean).join(" · ");
    }
    var hiddenSections = new Set(["Profile", "Rules", "Calculus", "Language", "Goals"]);
    var visibleSections = sections.filter(function (section) { return !hiddenSections.has(section.title); });
    var statusClass = tone === "error" ? "statusError" : "target";
    var statusHtml = display && tone === "error"
      ? "<div class='" + statusClass + "'>" + esc(display.status) + "</div>"
      : "";
    var hasMeaningfulDisplay = !!display && (
      tone === "error" ||
      !!display.title ||
      !!display.status ||
      visibleSections.length > 0
    );

    if (!goals.length) {
      root.className = hasMeaningfulDisplay ? "" : "empty";
      root.innerHTML = hasMeaningfulDisplay
        ? "<div class='goal " + (tone === "error" ? "goalError" : "") + "'>"
          + (tone === "error" ? "<div class='errorLabel'>Error</div>" : "")
          + (display && display.title ? "<div class='goalId'><b>" + esc(display.title) + "</b></div>" : "")
          + statusHtml
          + visibleSections.map(function (section) {
              return "<div class='sectionTitle'>" + esc(section.title) + "</div>"
                + "<ul>" + (section.body || []).map(function (item) {
                    return "<li class='hyp'>" + renderFormulaHtml(item) + "</li>";
                  }).join("") + "</ul>";
            }).join("")
          + "</div>"
        : "No proof state.";
      return;
    }

    root.className = "";
    var showDisplayCard = !!display && (tone === "error" || visibleSections.length > 0);
    var displayHtml = showDisplayCard
      ? "<div class='goal " + (tone === "error" ? "goalError" : "") + "'>"
          + (tone === "error" ? "<div class='errorLabel'>Error</div>" : "")
          + (display && display.title ? "<div class='goalId'><b>" + esc(display.title) + "</b></div>" : "")
          + (tone === "error" ? "<div class='" + statusClass + "'>" + esc(display.status) + "</div>" : "")
          + visibleSections.map(function (section) {
              return "<div class='sectionTitle'>" + esc(section.title) + "</div>"
                + "<ul>" + (section.body || []).map(function (item) {
                    return "<li class='hyp'>" + renderFormulaHtml(item) + "</li>";
                  }).join("") + "</ul>";
            }).join("")
          + "</div>"
      : "";

    root.innerHTML = displayHtml + goals.map(function (g, i) {
      var hyps = g.hypotheses || [];
      var leftTitle = isSequent ? "Left" : "Hypotheses";
      var rightTitle = isSequent ? "Right" : "Goal";
      var hypsHtml = hyps.length
        ? "<ul>" + hyps.map(function (h) {
            return "<li class='hyp'><code>" + esc(h.name) + "</code> : " + renderFormulaHtml(h.type) + "</li>";
          }).join("") + "</ul>"
        : "<div class='empty'>" + (isSequent ? "Empty antecedent." : "No hypotheses.") + "</div>";
      var label = isSequent
        ? "Sequent " + (i + 1)
        : (g.id ? esc(g.id) : "Goal " + (i + 1));

      if (isSequent) {
        return "<div class='goal'>"
          + "<div class='goalId'><b>" + label + "</b></div>"
          + "<div class='sequent'>"
          + "<div class='sequentSide'>"
          + "<div class='sectionTitle'>" + leftTitle + "</div>"
          + hypsHtml
          + "</div>"
          + "<div class='turnstile'>⊢</div>"
          + "<div class='sequentSide'>"
          + "<div class='sectionTitle'>" + rightTitle + "</div>"
          + "<div class='target'>" + renderFormulaHtml(g.target || "") + "</div>"
          + "</div>"
          + "</div>"
          + "</div>";
      }

      return "<div class='goal'>"
        + "<div class='goalId'><b>" + label + "</b></div>"
        + "<div class='sectionTitle'>" + leftTitle + "</div>"
        + hypsHtml
        + "<div class='sectionTitle'>" + rightTitle + "</div>"
        + "<div class='target'>" + renderFormulaHtml(g.target || "") + "</div>"
        + "</div>";
    }).join("");
  }

  window.mypaProofStateRenderer = {
    clearProofState: clear,
    renderProofState: render,
  };
})();
