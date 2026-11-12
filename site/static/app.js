(function () {
  var root = document.documentElement;

  var theme = document.querySelector(".theme");
  if (theme) theme.addEventListener("click", function () {
    var dark = root.getAttribute("data-theme") === "dark" ||
      (!root.getAttribute("data-theme") && window.matchMedia("(prefers-color-scheme: dark)").matches);
    var next = dark ? "light" : "dark";
    root.setAttribute("data-theme", next);
    try { localStorage.setItem("stein-theme", next); } catch (e) { /* ignore */ }
  });

  var toggle = document.querySelector(".toc-toggle");
  if (toggle) toggle.addEventListener("click", function () {
    document.body.classList.toggle("toc-open");
  });
  document.querySelectorAll(".toc a").forEach(function (a) {
    a.addEventListener("click", function () { document.body.classList.remove("toc-open"); });
  });

  function closeMenus(except) {
    document.querySelectorAll("details.dd[open], details.menu[open]").forEach(function (d) {
      if (d !== except) d.open = false;
    });
  }
  document.addEventListener("click", function (ev) {
    var d = ev.target.closest && ev.target.closest("details.dd, details.menu");
    closeMenus(d);
  });
  document.addEventListener("keydown", function (ev) { if (ev.key === "Escape") closeMenus(null); });

  var table = document.querySelector("table.results tbody tr[data-label]") ? document.querySelector("table.results:not(.main-results)") : null;
  if (table) {
    var q = document.getElementById("q");
    var chips = document.querySelectorAll(".filters .chip");
    var fRef = document.getElementById("f-refuted");
    var fNew = document.getElementById("f-new");
    var fPaper = document.getElementById("f-paper");
    var fBound = document.getElementById("f-boundary");
    var fNamed = document.getElementById("f-named");
    var fCh = document.getElementById("f-ch");
    var count = document.querySelector(".filter-count");
    var rows = table.querySelectorAll("tbody tr[data-label]");
    var filter = "";
    var readHash = function () {
      var h = new URLSearchParams(location.hash.slice(1));
      if (h.has("f")) filter = h.get("f");
      if (fCh && h.has("ch")) fCh.value = h.get("ch");
      if (fRef) fRef.checked = (h.get("m") || "").split(",").indexOf("refuted") >= 0;
      if (fNew) fNew.checked = (h.get("m") || "").split(",").indexOf("new-proof") >= 0;
      if (fPaper) fPaper.checked = (h.get("m") || "").split(",").indexOf("fails-paper") >= 0;
      if (fBound) fBound.checked = (h.get("m") || "").split(",").indexOf("boundary") >= 0;
      if (fNamed && h.has("all")) fNamed.checked = h.get("all") !== "1";
      if (q && h.has("q")) q.value = h.get("q");
      chips.forEach(function (x) {
        var on = x.dataset.filter === filter;
        x.classList.toggle("on", on);
        x.setAttribute("aria-pressed", on ? "true" : "false");
      });
    };
    var writeHash = function () {
      var h = new URLSearchParams();
      if (filter) h.set("f", filter);
      if (fCh && fCh.value) h.set("ch", fCh.value);
      var m = [];
      if (fRef && fRef.checked) m.push("refuted");
      if (fNew && fNew.checked) m.push("new-proof");
      if (fPaper && fPaper.checked) m.push("fails-paper");
      if (fBound && fBound.checked) m.push("boundary");
      if (m.length) h.set("m", m.join(","));
      if (fNamed && !fNamed.checked && fNamed.defaultChecked) h.set("all", "1");
      if (fNamed && fNamed.checked && !fNamed.defaultChecked) h.set("all", "0");
      if (q && q.value.trim()) h.set("q", q.value.trim());
      var s = h.toString();
      history.replaceState(null, "", s ? "#" + s : location.pathname + location.search);
    };
    var apply = function () {
      var text = q ? q.value.trim().toLowerCase() : "";
      var n = 0;
      rows.forEach(function (r) {
        var mk = " " + (r.dataset.markers || "") + " ";
        var ok = (!filter || r.dataset.label === filter) &&
          (!text || r.dataset.search.indexOf(text) >= 0) &&
          (!fRef || !fRef.checked || mk.indexOf(" refuted ") >= 0) &&
          (!fNew || !fNew.checked || mk.indexOf(" new-proof ") >= 0) &&
          (!fPaper || !fPaper.checked || mk.indexOf(" fails-paper ") >= 0) &&
          (!fBound || !fBound.checked || mk.indexOf(" boundary ") >= 0) &&
          (!fNamed || !fNamed.checked || r.dataset.named === "1") &&
          (!fCh || !fCh.value || r.dataset.ch === fCh.value);
        r.hidden = !ok;
        if (ok) n++;
      });
      table.querySelectorAll("tr.ch-row").forEach(function (h) {
        var x = h.nextElementSibling, any = false;
        while (x && !x.classList.contains("ch-row")) { if (!x.hidden) { any = true; break; } x = x.nextElementSibling; }
        h.hidden = !any;
      });
      if (count) count.textContent = n + " of " + rows.length + " items shown";
    };
    var changed = function () { writeHash(); apply(); };
    if (q) {
      var params = new URLSearchParams(location.search);
      if (params.get("q")) q.value = params.get("q");
      q.addEventListener("input", changed);
    }
    [fRef, fNew, fPaper, fBound, fNamed, fCh].forEach(function (el) { if (el) el.addEventListener("change", changed); });
    chips.forEach(function (c) {
      c.addEventListener("click", function () {
        filter = c.dataset.filter;
        chips.forEach(function (x) {
          x.classList.toggle("on", x === c);
          x.setAttribute("aria-pressed", x === c ? "true" : "false");
        });
        changed();
      });
    });
    if (/^#(n|r)-/.test(location.hash)) {
      if (fNamed) fNamed.checked = false;
    } else {
      readHash();
    }
    apply();
    window.addEventListener("hashchange", function () {
      if (!/^#(n|r)-/.test(location.hash)) { readHash(); apply(); }
    });
  }

  var graph = document.querySelector("svg.depgraph");
  if (graph) {
    var gNamed = document.getElementById("g-named");
    var gCh = document.getElementById("g-ch");
    var info = document.getElementById("g-info");
    var wrap = graph.parentNode;
    var nodes = graph.querySelectorAll("g.gn[data-id]");
    var byId = {};
    nodes.forEach(function (g) { byId[g.dataset.id] = g; });
    var scale = 1, selected = null;
    var named = function () { return !gNamed || gNamed.checked; };
    var size = function () {
      var w = +graph.dataset.w, h = +(named() ? graph.dataset.hNamed : graph.dataset.hAll);
      graph.setAttribute("viewBox", "0 0 " + w + " " + h);
      graph.setAttribute("width", Math.round(w * scale));
      graph.setAttribute("height", Math.round(h * scale));
    };
    var layout = function () {
      var only = named();
      graph.classList.toggle("named-only", only);
      nodes.forEach(function (g) {
        var xy = (only ? g.dataset.nxy : g.dataset.xy).split(",");
        g.setAttribute("transform", "translate(" + xy[0] + "," + xy[1] + ")");
        g.parentNode.style.display = (only && g.dataset.named !== "1") ? "none" : "";
      });
      size();
      highlight(selected);
    };
    var usesOf = function (id) {
      var g = byId[id];
      if (!g) return [];
      var s = named() ? g.dataset.nuses : g.dataset.uses;
      return s ? s.split(" ") : [];
    };
    var citedBy = function (id) {
      var out = [];
      nodes.forEach(function (g) { if (usesOf(g.dataset.id).indexOf(id) >= 0) out.push(g.dataset.id); });
      return out;
    };
    var closure = function (id, step) {
      var seen = {}, stack = [id];
      while (stack.length) {
        var x = stack.pop();
        step(x).forEach(function (y) { if (!seen[y]) { seen[y] = true; stack.push(y); } });
      }
      return seen;
    };
    function highlight(id) {
      selected = id;
      var ch = gCh ? gCh.value : "";
      var up = id ? closure(id, usesOf) : {}, down = id ? closure(id, citedBy) : {};
      nodes.forEach(function (g) {
        var x = g.dataset.id;
        var inCh = !ch || g.dataset.ch === ch;
        var lit = id ? (x === id || up[x] || down[x]) : inCh;
        g.classList.toggle("dim", !lit);
        g.classList.toggle("sel", x === id);
        g.classList.toggle("anc", !!(id && up[x]));
        g.classList.toggle("desc", !!(id && down[x]));
      });
      graph.querySelectorAll(".gn-edge").forEach(function (e) {
        var cls = e.classList.contains(named() ? "e-named" : "e-all");
        e.style.display = cls ? "" : "none";
        var a = e.dataset.from, b = e.dataset.to;
        var lit = id ? ((up[a] || a === id) && (up[b] || b === id)) || ((down[a] || a === id) && (down[b] || b === id))
          : (!ch || (byId[a] && byId[a].dataset.ch === ch) || (byId[b] && byId[b].dataset.ch === ch));
        e.classList.toggle("hl", !!id && lit);
        e.classList.toggle("dim", !lit);
      });
      if (info) {
        if (id) {
          var t = byId[id].parentNode.getAttribute("aria-label") || id;
          info.innerHTML = "";
          var a = document.createElement("a");
          a.href = "#n-" + id;
          a.textContent = t;
          info.appendChild(a);
          info.appendChild(document.createTextNode(": uses " + Object.keys(up).length + ", used by " +
            Object.keys(down).length + " (transitively)"));
        } else {
          info.textContent = "";
        }
      }
    }
    nodes.forEach(function (g) {
      g.parentNode.addEventListener("click", function (ev) {
        if (selected !== g.dataset.id) { ev.preventDefault(); highlight(g.dataset.id); }
      });
    });
    if (gNamed) gNamed.addEventListener("change", layout);
    if (gCh) gCh.addEventListener("change", function () {
      highlight(null);
      var t = graph.querySelector('.gn-col[data-ch="' + gCh.value + '"]');
      if (t) wrap.scrollLeft = Math.max(0, (+t.getAttribute("x")) * scale - 12);
    });
    var zoom = function (f) { scale = Math.min(2.5, Math.max(0.4, scale * f)); size(); };
    var zi = document.getElementById("g-zoom-in"), zo = document.getElementById("g-zoom-out"), gc = document.getElementById("g-clear");
    if (zi) zi.addEventListener("click", function () { zoom(1.25); });
    if (zo) zo.addEventListener("click", function () { zoom(0.8); });
    if (gc) gc.addEventListener("click", function () { if (gCh) gCh.value = ""; highlight(null); });
    layout();
  }

  function reveal() {
    if (!location.hash || location.hash.indexOf("=") >= 0) return;
    var id = decodeURIComponent(location.hash.slice(1));
    var el = document.getElementById(id) || document.getElementById(id.replace(/[^A-Za-z0-9:_.\-]/g, "_"));
    if (!el) return;
    if (el.id !== id && el.scrollIntoView) el.scrollIntoView();
    for (var p = el.parentElement; p; p = p.parentElement) if (p.tagName === "DETAILS") p.open = true;
    if (el.tagName === "ARTICLE") {
      var d = el.querySelector("details");
      if (d) d.open = true;
      el.scrollIntoView();
    }
  }
  window.addEventListener("hashchange", reveal);
  reveal();
})();
