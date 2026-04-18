(function () {
  function keyFor(line, character) {
    return String(line) + ":" + String(character);
  }

  function buildPositionMap(positions) {
    var map = new Map();
    for (var i = 0; i < positions.length; i += 1) {
      var entry = positions[i];
      map.set(keyFor(entry.line, entry.character), entry);
    }
    return map;
  }

  function offsetToPosition(text, offset) {
    var bounded = Math.max(0, Math.min(offset, text.length));
    var line = 0;
    var character = 0;
    for (var i = 0; i < bounded; i += 1) {
      if (text[i] === "\n") {
        line += 1;
        character = 0;
      } else {
        character += 1;
      }
    }
    return { line: line, character: character };
  }

  function renderBadge(statuses) {
    if (!Array.isArray(statuses) || !statuses.length) {
      return "";
    }
    var allVerified = statuses.every(function (status) { return !!status.verified; });
    if (!allVerified) {
      return "<span class='mypa-status mypa-status-warn'>Unchecked</span>";
    }
    return "<span class='mypa-status mypa-status-ok'>Verified</span>";
  }

  function initWidget(widget) {
    var raw = widget.querySelector("script[type='application/json']");
    if (!raw) {
      return;
    }

    var payload = JSON.parse(raw.textContent);
    var positions = buildPositionMap(payload.positions || []);
    var editor = widget.querySelector(".mypa-editor");
    var goalsRoot = widget.querySelector(".mypa-goals-root");
    var goalsMeta = widget.querySelector(".mypa-goals-meta");
    var cursorLabel = widget.querySelector(".mypa-cursor");
    var headerMeta = widget.querySelector(".mypa-demo-meta");
    var source = String(payload.source || "");

    editor.value = source;
    editor.setAttribute("readonly", "readonly");
    headerMeta.innerHTML = renderBadge(payload.theoremStatuses) + "<span>" + source.split("\n").length + " lines</span>";

    function updateFromOffset(offset) {
      var pos = offsetToPosition(source, offset);
      var cached = positions.get(keyFor(pos.line, pos.character));
      if (!cached) {
        return;
      }
      cursorLabel.textContent = "Cursor " + (pos.line + 1) + ":" + (pos.character + 1) + " · " + cached.kind.replace("_", " ");
      window.mypaProofStateRenderer.renderProofState(goalsRoot, goalsMeta, cached.state);
    }

    editor.addEventListener("click", function () {
      updateFromOffset(editor.selectionStart || 0);
    });
    editor.addEventListener("keyup", function () {
      updateFromOffset(editor.selectionStart || 0);
    });
    editor.addEventListener("select", function () {
      updateFromOffset(editor.selectionStart || 0);
    });

    updateFromOffset(0);
  }

  document.addEventListener("DOMContentLoaded", function () {
    var widgets = document.querySelectorAll(".mypa-widget");
    for (var i = 0; i < widgets.length; i += 1) {
      initWidget(widgets[i]);
    }
  });
})();
