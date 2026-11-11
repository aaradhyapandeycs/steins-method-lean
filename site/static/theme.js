// Apply a saved light/dark choice before first paint. Storage may be unavailable.
(function () {
  try {
    var t = localStorage.getItem("sfrl-theme");
    if (t === "light" || t === "dark") document.documentElement.setAttribute("data-theme", t);
  } catch (e) { /* ignore */ }
})();
