/* ==========================================================================
   book.js — shared behaviour layer for every chapter.
   Loaded at the END of <body>, after each page's inline script, so all
   page content (proof blocks, MCQs, worksheet) already exists.
   Everything is feature-detected: a page without a visualiser, worksheet,
   or quiz simply skips those parts.
   ========================================================================== */
(function () {
  "use strict";
  var byId = function (id) { return document.getElementById(id); };
  var qs  = function (s, r) { return (r || document).querySelector(s); };
  var qsa = function (s, r) { return Array.prototype.slice.call((r || document).querySelectorAll(s)); };
  var page = (location.pathname.split("/").pop() || "cover.html").toLowerCase() || "cover.html";
  if (qs(".topnav")) return; // already initialised

  /* ---------- helpers ---------- */
  function el(tag, cls, html) { var e = document.createElement(tag); if (cls) e.className = cls; if (html !== undefined) e.innerHTML = html; return e; }
  function store(key, val) { try { localStorage.setItem(key, JSON.stringify(val)); } catch (e) {} }
  function load(key, dflt) { try { return JSON.parse(localStorage.getItem(key)) || dflt; } catch (e) { return dflt; } }
  function rnum(minLen, maxLen) {
    var len = minLen + Math.floor(Math.random() * (maxLen - minLen + 1)), s = String(1 + Math.floor(Math.random() * 9));
    for (var i = 1; i < len; i++) s += Math.floor(Math.random() * 10);
    return s;
  }

  /* ---------- per-page configuration ---------- */
  var TITLES = {
    "prologue": "Ch 0 · Reading Lean Code", "addition": "Ch 1 · Vertical Addition",
    "subtraction": "Ch 2 · Vertical Subtraction", "multiplication": "Ch 3 · Long Multiplication",
    "division": "Ch 4 · Long Division", "divisibility": "Ch 5 · Divisibility Tests",
    "gcd": "Ch 6 · Euclid's GCD", "cuberoot": "Ch 7 · The Cube-Root Trick",
    "squareroot": "Ch 8 · Square Roots by Hand"
  };
  var OPLABELS = ["Describe", "Lean", "Run", "Think", "Proof", "Test", "Write"];
  var CONFIG = {
    "prologue.html": {
      key: "prologue", ch: "Ch 0 · Reading Lean Code", mins: 15, dots: "●○○○", note: "start here — no Lean assumed", hint: false,
      labels: ["Every input", "Notation", "Tactics", "Numbers", "First proof"], proofSel: null, rand: null,
      objectives: [
        "read the small set of notations every chapter uses — lists, <code>⟨⟩</code> digits, pattern matching;",
        "meet the handful of tactics that do almost all the work, each with a tiny example;",
        "see how a number is stored, and follow your first two real proofs."],
      summary: [
        "Lean code here is pattern matching on digit lists; <code>⟨d, proof⟩</code> carries a digit together with the fact <code>d &lt; 10</code>;",
        "a proof is a sequence of tactics, each transforming the goal until nothing is left;",
        "<code>toNat</code> / <code>fromNat</code> convert between lists and numbers — and their round-trip proof is induction + <code>simp</code> + <code>omega</code>."],
      next: { href: "addition.html", nu: "Next up · Ch 1", nt: "Vertical Addition — the first algorithm, proved correct →" }
    },
    "addition.html": {
      key: "addition", ch: "Ch 1 · Vertical Addition", mins: 25, dots: "●○○○", note: "first chapter — no Lean experience assumed",
      labels: ["Describe", "Lean", "Run", "Proof", "Test", "Write"], proofSel: "#proofAdd",
      rand: function () { byId("opA").value = rnum(2, 4); byId("opB").value = rnum(2, 4); },
      objectives: [
        "see the school algorithm as a three-layer Lean program;",
        "watch its carry invariant hold, column by column;",
        "read a real induction proof — and write your first lines of Lean."],
      summary: [
        "a number is a list of digits, read back by <code>toNat</code>; the algorithm is three layers — table, column, list;",
        "the carry invariant <code>aₖ + bₖ = resultₖ + carry × 10ᵏ</code> is what “correct” means mid-run;",
        "the proof mirrors the code: brute force for the finite layers, induction (generalising the carry) for the list."],
      next: { href: "subtraction.html", nu: "Next up · Ch 2", nt: "Vertical Subtraction — the same shape with a borrow, and a real precondition →" }
    },
    "subtraction.html": {
      key: "subtraction", ch: "Ch 2 · Vertical Subtraction", mins: 25, dots: "●●○○", note: "builds directly on the addition chapter",
      labels: OPLABELS, proofSel: "#proofSub",
      rand: function () { var x = rnum(2, 4), y = rnum(2, 4); if (BigInt(x) < BigInt(y)) { var t = x; x = y; y = t; } byId("opA").value = x; byId("opB").value = y; },
      objectives: [
        "reuse addition's three-layer shape, with a borrow in place of the carry;",
        "meet the first <em>precondition</em>: the top number must be at least the bottom;",
        "watch the proof re-earn that precondition at every column."],
      summary: [
        "the borrow mirrors the carry, and the algorithm keeps addition's table → column → list shape;",
        "subtraction is only defined when <code>b ≤ a</code> — the theorem carries that hypothesis everywhere;",
        "the induction must re-prove the precondition on the tails before it can recurse — this chapter's one new proof move."],
      next: { href: "multiplication.html", nu: "Next up · Ch 3", nt: "Long Multiplication — partial products and shifts, on top of verified addition →" }
    },
    "multiplication.html": {
      key: "multiplication", ch: "Ch 3 · Long Multiplication", mins: 30, dots: "●●○○", note: "reuses the addition chapter as a subroutine",
      labels: OPLABELS, proofSel: "#proofMul",
      rand: function () { byId("opA").value = rnum(2, 3); byId("opB").value = rnum(2, 3); },
      objectives: [
        "break long multiplication into a times table, digit multiplication, and shifted partial products;",
        "watch each partial product slide into place and sum to <code>a × b</code>;",
        "see the proof cite the addition chapter as a subroutine rather than re-prove it."],
      summary: [
        "<code>a × b = Σ (a × bᵢ) × 10ⁱ</code> — the distributive law <em>is</em> the algorithm;",
        "shifting left is multiplying by ten: prepend a zero to the digit list;",
        "each layer's proof feeds the next, and the final sum is closed by <code>verticalAdd_correct</code> — addition, cited not reproved."],
      next: { href: "division.html", nu: "Next up · Ch 4", nt: "Long Division — the trial-digit search and the running remainder →" }
    },
    "division.html": {
      key: "division", ch: "Ch 4 · Long Division", mins: 35, dots: "●●●○", note: "the hardest of the four operations",
      labels: OPLABELS, proofSel: "#proofDiv",
      rand: function () { byId("opA").value = rnum(3, 5); byId("opB").value = String(2 + Math.floor(Math.random() * 8)); },
      objectives: [
        "run the classic bring-down / trial-digit / subtract loop from the top digit down;",
        "see why “the largest digit that fits” is exactly what keeps the remainder small;",
        "follow the invariant <code>value = quotient × divisor + remainder</code> through the proof."],
      summary: [
        "division works top-down, so the list is reversed, processed, and reversed back;",
        "the trial digit's two bounds — <code>q·b ≤ v &lt; (q+1)·b</code> — make the subtraction safe and force the new remainder below <code>b</code>;",
        "the helper's induction carries the defining equation to the end; <code>b ≠ 0</code> is a hypothesis, like subtraction's precondition."],
      next: { href: "divisibility.html", nu: "Next up · Ch 5", nt: "Divisibility Tests — why the rules for 3, 9 and 11 work →" }
    },
    "divisibility.html": {
      key: "divisibility", ch: "Ch 5 · Divisibility Tests", mins: 30, dots: "●●●○", note: "new tool: modular arithmetic",
      labels: OPLABELS, proofSel: "#proofDiv",
      rand: function () { byId("opA").value = rnum(3, 6); },
      objectives: [
        "learn the digit tests for 2, 5, 3, 9 and 11 — and the modular arithmetic behind them;",
        "watch a number and its digit summary stay congruent, suffix by suffix;",
        "prove the ÷9 and ÷11 tests through <code>10 ≡ 1</code> and <code>10 ≡ −1</code>."],
      summary: [
        "remainders survive <code>+</code> and <code>×</code>, so a number's remainder is built from its digits' remainders;",
        "<code>10 ≡ 0</code> (mod 2, 5), <code>10 ≡ 1</code> (mod 3, 9), <code>10 ≡ −1</code> (mod 11) give the units digit, the digit sum, and the alternating sum;",
        "<code>myMod</code> bridges to <code>Nat.mod</code> through <code>longDiv</code> — the previous chapter doing this one's work."],
      next: { href: "gcd.html", nu: "Next up · Ch 6", nt: "Euclid's GCD — repeated subtraction as rectangle tiling →" }
    },
    "gcd.html": {
      key: "gcd", ch: "Ch 6 · Euclid's GCD", mins: 25, dots: "●●●○", note: "first termination proof; functional induction",
      labels: OPLABELS, proofSel: "#proofGcd",
      rand: function () { var g = 2 + Math.floor(Math.random() * 11); var m = function () { return g * (2 + Math.floor(Math.random() * 7)); }; byId("opA").value = m(); byId("opB").value = m(); },
      objectives: [
        "see Euclid's subtractive gcd as carving the largest square tile from a rectangle;",
        "meet the book's first termination proof — a measure that must be shown to shrink;",
        "prove the algorithm equals <code>Nat.gcd</code> by <em>functional induction</em>."],
      summary: [
        "<code>gcd(a, b) = gcd(a − b, b)</code>: subtracting the smaller side leaves the answer unchanged;",
        "the recursion shrinks numbers, not lists, so Lean needs an explicit decreasing measure — proved with Chapter 2's subtraction theorem;",
        "functional induction gives one goal per branch of the definition, the hypothesis waiting at each recursive call."],
      next: { href: "cuberoot.html", nu: "Next up · Ch 7", nt: "The Cube-Root Trick — the mental party trick, proved correct →" }
    },
    "cuberoot.html": {
      key: "cuberoot", ch: "Ch 7 · The Cube-Root Trick", mins: 20, dots: "●●○○", note: "easy trick, the book's deepest proof",
      labels: OPLABELS, proofSel: "#proofCube",
      rand: function () { var n = 1 + Math.floor(Math.random() * 99); byId("opA").value = String(n * n * n); },
      objectives: [
        "learn the two-glance mental trick for cube roots of perfect cubes up to six digits;",
        "see the units lookup as a bijection and the tens digit as a descending cube search;",
        "prove it correct <em>twice</em> — by exhaustion, and structurally."],
      summary: [
        "the units digit of a cube fixes the root's units digit (a bijection: 2↔8, 3↔7, the rest fixed);",
        "dropping the last three digits leaves a³ on top, so a descending cube search gives the tens digit;",
        "finiteness allows a brute-force proof (interval_cases + native_decide); the structural proof shows <em>why</em> each glance is sound."],
      next: { href: "squareroot.html", nu: "Next up · Ch 8", nt: "Square Roots by Hand — the pen-and-paper method, proved to give the floor →" }
    },
    "squareroot.html": {
      key: "squareroot", ch: "Ch 8 · Square Roots by Hand", mins: 35, dots: "●●●●", note: "the hardest chapter — everything before it, at once",
      labels: OPLABELS, proofSel: "#proofSqrt",
      rand: function () { byId("opA").value = String(2 + Math.floor(Math.random() * 9998)); },
      objectives: [
        "run the pen-and-paper square-root method: pair the digits, then find each root digit in turn;",
        "see why the digit you append subtracts exactly <code>(2q·10 + x)·x</code> — the <code>(10q + x)²</code> expansion;",
        "follow the floor-√ proof — <code>q² ≤ a &lt; (q+1)²</code> — built on division, multiplication and subtraction together."],
      summary: [
        "digits pair off from the right (base 100), one root digit per pair;",
        "each step doubles the root so far and searches for the largest <code>x</code> with <code>(2q·10 + x)·x ≤</code> the brought-down remainder — a trial divisor that grows with the trial digit;",
        "the maintained bound <code>r ≤ 2q</code>, plus <code>(10q+x)² = (2q·10+x)·x + 100q²</code>, give <code>q² + r = a</code> and <code>q = ⌊√a⌋</code>."],
      next: { href: "epilogue.html", nu: "Last page", nt: "Epilogue — what you built, and where it goes →" }
    },
    "epilogue.html": {
      key: "epilogue", ch: "Epilogue", mins: 5, dots: "", note: "the closing page", proofSel: null,
      labels: ["What you did", "Where it goes", "Next steps"],
      next: { href: "cover.html", nu: "The end", nt: "Back to the contents →" }
    }
  };

  /* ---------- the recurring paradigm each chapter adds to the thread ---------- */
  var PARADIGM = {
    "addition": "Invariant &amp; induction — and generalizing the hypothesis so the induction goes through.",
    "subtraction": "Preconditions — a theorem that holds only under a stated assumption, re-earned at every step.",
    "multiplication": "Composition — a verified operation built out of verified sub-operations.",
    "division": "A loop invariant with a two-sided bound: value = q·b + r, and r &lt; b.",
    "divisibility": "Specification as an equivalence (iff), reduced to a trusted tool — modular arithmetic.",
    "gcd": "Termination — proving a recursion ends, via a measure that strictly decreases.",
    "cuberoot": "One theorem, two proofs — brute force versus structure.",
    "squareroot": "Every paradigm at once — invariant, precondition, two-sided bound, and place-value algebra."
  };

  /* ---------- cover page: visited badges + continue button ---------- */
  if (page === "cover.html" || page === "") {
    var bp = load("bookprogress", {});
    var lastKey = null, lastT = 0;
    Object.keys(TITLES).forEach(function (k) {
      if (bp[k] && bp[k].visited) {
        var a = qs('.toc a[href="' + k + '.html"]');
        var b = a && a.querySelector(".badge");
        if (b) b.insertAdjacentHTML("beforebegin", '<span class="badge visit">✓ visited</span>');
        if (bp[k].t > lastT) { lastT = bp[k].t; lastKey = k; }
      }
    });
    var cta = qs(".cta");
    if (cta && lastKey) { cta.href = lastKey + ".html"; cta.textContent = "Continue reading — " + TITLES[lastKey] + " →"; }
    return;
  }

  var cfg = CONFIG[page];
  if (!cfg) return;

  /* ---------- section ids ---------- */
  var h2s = qsa(".wrap h2");
  h2s.forEach(function (h, i) { if (!h.id) h.id = "s" + (i + 1); });

  /* ---------- sticky top nav ---------- */
  var nav = el("nav", "topnav");
  nav.setAttribute("aria-label", "chapter sections");
  var tn = el("div", "tn");
  var brand = el("a", "brand", "Learn2Lean"); brand.href = "cover.html"; brand.title = "Contents"; tn.appendChild(brand);
  var home = el("a", "home", "← Contents"); home.href = "cover.html"; tn.appendChild(home);
  h2s.forEach(function (h, i) {
    var a = el("a", "sec", (i + 1) + " " + (cfg.labels[i] || ""));
    a.href = "#" + h.id; tn.appendChild(a);
  });
  tn.appendChild(el("span", "chip", cfg.ch));
  nav.appendChild(tn);
  document.body.insertBefore(nav, document.body.firstChild);

  /* ---------- reference drawer: an in-page cheatsheet (no second tab) ---------- */
  var CHEAT = {
    tactics: [
      { t: "rfl", c: "0", d: "closes a goal that holds by definition — both sides compute to the same thing." },
      { t: "decide", c: "0", d: "settles a goal that is a finite, computable yes/no question." },
      { t: "native_decide", c: "7", d: "like decide, but compiled to fast native code — for big finite checks." },
      { t: "simp", c: "0", d: "simplifies the goal with rewrite rules; simp [f] also unfolds f." },
      { t: "simpa", c: "1", d: "simp, then finish with a supplied term — simpa using h." },
      { t: "omega", c: "0", d: "solves linear arithmetic over the naturals and integers." },
      { t: "rw", c: "0", d: "rewrites the goal with an equation, left to right — rw [h]." },
      { t: "ring", c: "3", d: "proves equalities that hold by the laws of + and × alone." },
      { t: "linarith", c: "8", d: "derives the goal from linear inequalities already in context." },
      { t: "nlinarith", c: "7", d: "linarith with some product reasoning — for quadratics." },
      { t: "calc", c: "4", d: "a chain of =/≤ steps, each separately justified." },
      { t: "intro", c: "0", d: "moves a hypothesis or ∀-variable out of the goal into context." },
      { t: "exact", c: "0", d: "closes the goal with a term of exactly its type." },
      { t: "refine", c: "1", d: "like exact, but leaves ?_ holes as new goals." },
      { t: "constructor", c: "1", d: "splits a goal like A ∧ B into its two parts." },
      { t: "obtain", c: "2", d: "destructures a hypothesis — obtain ⟨x, hx⟩ := h." },
      { t: "rcases", c: "4", d: "case-splits and destructures in one step." },
      { t: "cases", c: "1", d: "splits a value into its possible constructors." },
      { t: "split", c: "4", d: "splits an if / match in the goal, one goal per branch." },
      { t: "fin_cases", c: "2", d: "replaces a finite variable (like a digit) with each concrete value." },
      { t: "interval_cases", c: "7", d: "splits a bounded number into every value in range." },
      { t: "induction", c: "0", d: "prove ∀ n by base case + step; on lists, nil + cons." },
      { t: "… using f.induct", c: "6", d: "functional induction: one case per branch of f's definition." },
      { t: "set", c: "8", d: "names a sub-expression and records its defining equation." },
      { t: "change", c: "8", d: "replaces the goal with a definitionally-equal one." },
      { t: "&lt;;&gt;", c: "2", d: "combinator: run the next tactic on every goal the last one produced." }
    ],
    notation: [
      { s: "[a, b, c]", d: "a list — here digits, least-significant first." },
      { s: "x :: xs", d: "a list with head x and tail xs (“cons”)." },
      { s: "⟨d, h⟩", d: "a digit: value d bundled with a proof h that d &lt; 10." },
      { s: "a → b", d: "a function from a to b (and, in logic, “implies”)." },
      { s: "f a b", d: "function application: f applied to a, then b." },
      { s: ":=", d: "“is defined as” — gives a definition or a value." },
      { s: "| pat =&gt;", d: "one case of a pattern match or recursive definition." },
      { s: "∀ x, P x", d: "“for all x, P”; ∃ x, P x is “there exists”." },
      { s: "A ∧ B", d: "“and”; ∨ is “or”, ↔ is “iff”, ¬ is “not”." },
      { s: "a ∣ b", d: "“a divides b” — b is a multiple of a." },
      { s: "a ≡ b [MOD n]", d: "a and b leave the same remainder mod n." },
      { s: "a % n", d: "remainder of a ÷ n; a ^ k is a to the power k." },
      { s: "⌊x⌋", d: "the floor — the greatest integer ≤ x." },
      { s: "⊢ goal", d: "the turnstile: what is left to prove right now." }
    ]
  };
  (function buildDrawer() {
    var btn = el("button", "refbtn", "📖 Reference"); btn.title = "Lean cheatsheet — opens here (press ?)";
    tn.insertBefore(btn, qs(".chip", tn) || null);
    function rows(arr, kind) {
      return arr.map(function (x) {
        return kind === "t"
          ? '<tr><td class="ct"><code>' + x.t + '</code></td><td class="cd">' + x.d + '</td><td class="cc">Ch ' + x.c + '</td></tr>'
          : '<tr><td class="cs"><code>' + x.s + '</code></td><td class="cd">' + x.d + '</td></tr>';
      }).join("");
    }
    var drawer = el("aside", "drawer");
    drawer.id = "refDrawer"; drawer.setAttribute("aria-hidden", "true"); drawer.setAttribute("aria-label", "Reference cheatsheet");
    drawer.innerHTML =
      '<div class="drawer-h"><b>Reference</b><span class="drawer-sub">stays with you — no need to leave the page</span><button class="drawer-x" aria-label="close">✕</button></div>' +
      '<div class="drawer-body">' +
        '<h4>Lean tactics <span class="small" style="text-transform:none;letter-spacing:0;color:var(--muted)">— “Ch” is where each first appears</span></h4>' +
        '<table class="cheat">' + rows(CHEAT.tactics, "t") + '</table>' +
        '<h4>Notation</h4>' +
        '<table class="cheat">' + rows(CHEAT.notation, "n") + '</table>' +
        '<p class="small" style="color:var(--muted)">Chapter 0 introduces every tactic with a worked example.</p>' +
      '</div>';
    var scrim = el("div", "drawer-scrim");
    document.body.appendChild(scrim); document.body.appendChild(drawer);
    var openD = function () { drawer.classList.add("open"); scrim.classList.add("open"); drawer.setAttribute("aria-hidden", "false"); };
    var closeD = function () { drawer.classList.remove("open"); scrim.classList.remove("open"); drawer.setAttribute("aria-hidden", "true"); };
    btn.onclick = openD; scrim.onclick = closeD; qs(".drawer-x", drawer).onclick = closeD;
    document.addEventListener("keydown", function (e) {
      if (e.key === "Escape") { closeD(); return; }
      var tg = (e.target || {}).tagName || "";
      if (e.key === "?" && !/INPUT|TEXTAREA|SELECT/.test(tg)) { drawer.classList.contains("open") ? closeD() : openD(); }
    });
  })();

  /* breadcrumb line is redundant under the sticky nav */
  var bc = qs(".wrap > p.sub");
  if (bc && /Contents/.test(bc.textContent) && bc.nextElementSibling && bc.nextElementSibling.tagName === "H1") bc.remove();

  /* ---------- chapter meta + objectives + tooltip hint ---------- */
  var h1 = qs(".wrap h1");
  var anchor = (h1 && h1.nextElementSibling && h1.nextElementSibling.classList.contains("sub")) ? h1.nextElementSibling : h1;
  if (anchor) {
    var frag = document.createDocumentFragment();
    frag.appendChild(el("div", "meta",
      "<span>~" + cfg.mins + " min</span><span class=\"dots\">" + cfg.dots + "</span><span>" + cfg.note + "</span>"));
    if (cfg.objectives) frag.appendChild(el("div", "objectives",
      '<div class="ot">In this chapter you will</div><ul>' + cfg.objectives.map(function (o) { return "<li>" + o + "</li>"; }).join("") + "</ul>"));
    if (PARADIGM[cfg.key]) frag.appendChild(el("div", "paradigm",
      '<span>Paradigm</span> ' + PARADIGM[cfg.key]));
    if (cfg.hint !== false && qs(".tok")) frag.appendChild(el("div", "hintbar",
      '💡 In any code block, <b>hover or tap</b> a <span style="color:var(--tac)">tactic</span> or ' +
      '<span style="color:var(--lem)">definition</span> to see what it does and the goal it leaves. ' +
      "Tap elsewhere (or press Esc) to close it."));
    anchor.parentNode.insertBefore(frag, anchor.nextSibling);
  }

  /* ---------- summary + next-up cards ---------- */
  var pager = qs(".pager");
  if (pager && cfg.summary) {
    var sum = el("div", "summary",
      '<div class="st">You now know</div><ul>' + cfg.summary.map(function (o) { return "<li>" + o + "</li>"; }).join("") + "</ul>");
    pager.parentNode.insertBefore(sum, pager);
    if (cfg.next) {
      var nu = el("a", "nextup", '<span class="nu">' + cfg.next.nu + '</span><div class="nt">' + cfg.next.nt + "</div>");
      nu.href = cfg.next.href;
      pager.parentNode.insertBefore(nu, pager);
    }
  }

  /* ---------- scrollspy + back-to-top ---------- */
  var secLinks = qsa(".topnav a.sec");
  function spy() {
    var y = window.scrollY + 90, cur = null;
    h2s.forEach(function (h) { if (h.offsetTop <= y) cur = h.id; });
    secLinks.forEach(function (a) { a.classList.toggle("on", a.getAttribute("href") === "#" + cur); });
  }
  var btt = el("button", "", "↑"); btt.id = "btt"; btt.title = "back to top"; btt.setAttribute("aria-label", "back to top");
  document.body.appendChild(btt);
  btt.onclick = function () { window.scrollTo({ top: 0, behavior: "smooth" }); };
  window.addEventListener("scroll", function () { spy(); btt.classList.toggle("show", window.scrollY > 700); }, { passive: true });
  spy();

  /* ---------- reading progress ---------- */
  var bp2 = load("bookprogress", {}); bp2[cfg.key] = { visited: true, t: Date.now() }; store("bookprogress", bp2);

  /* ---------- tooltips: rebind with tap-to-pin + keyboard ---------- */
  var tip = byId("tip");
  if (tip && qs(".tok")) {
    qsa(".tok").forEach(function (old) { old.replaceWith(old.cloneNode(true)); }); // drop page's hover-only listeners
    var pinned = null;
    var showTip = function (elm) {
      tip.innerHTML = "";
      tip.appendChild(el("div", "th", "")); tip.firstChild.textContent = elm.dataset.th || "";
      if (elm.dataset.goal) { var g = el("div", "goal"); g.textContent = "⊢ " + elm.dataset.goal; tip.appendChild(g); }
      if (elm.dataset.note) { var n = el("div", "note2"); n.textContent = elm.dataset.note; tip.appendChild(n); }
      tip.style.display = "block";
    };
    var placeAt = function (x, y) {
      var pad = 14, px = x + pad, w = tip.offsetWidth, vw = window.innerWidth + window.scrollX;
      if (px + w > vw) px = Math.max(8, x - w - pad);
      tip.style.left = px + "px"; tip.style.top = (y + pad) + "px";
    };
    var placeByEl = function (elm) { var r = elm.getBoundingClientRect(); placeAt(r.left + window.scrollX, r.bottom + window.scrollY - 8); };
    var hideTip = function () { tip.style.display = "none"; if (pinned) { pinned.classList.remove("pinned"); pinned = null; } };
    qsa(".tok").forEach(function (elm) {
      elm.tabIndex = 0;
      elm.addEventListener("mouseenter", function () { if (!pinned) showTip(elm); });
      elm.addEventListener("mousemove", function (e) { if (!pinned) placeAt(e.pageX, e.pageY); });
      elm.addEventListener("mouseleave", function () { if (!pinned) tip.style.display = "none"; });
      elm.addEventListener("click", function (e) {
        e.stopPropagation();
        if (pinned === elm) { hideTip(); return; }
        if (pinned) pinned.classList.remove("pinned");
        pinned = elm; elm.classList.add("pinned"); showTip(elm); placeByEl(elm);
      });
      elm.addEventListener("focus", function () { showTip(elm); placeByEl(elm); });
      elm.addEventListener("blur", function () { if (pinned !== elm) tip.style.display = "none"; });
    });
    document.addEventListener("click", function () { if (pinned) hideTip(); });
    document.addEventListener("keydown", function (e) { if (e.key === "Escape") hideTip(); });
  }

  /* ---------- quizzes: shuffle, persist, progress badge ---------- */
  var mcqs = qsa('div[id$="MCQ"]');
  if (mcqs.length) {
    var QK = "bookquiz:" + cfg.key;
    var doneSet = load(QK, {});
    var badge = el("span", "quizprog");
    var quizH2 = h2s.filter(function (h) { return /Test the ideas|Did the proof land/.test(h.textContent); })[0];
    if (quizH2) quizH2.appendChild(badge);
    var updateBadge = function () { badge.textContent = Object.keys(load(QK, {})).length + " / " + mcqs.length + " answered"; };
    var shuffleOpts = function (c) {
      var opts = qsa("button.opt", c);
      for (var i = opts.length - 1; i > 0; i--) { var j = Math.floor(Math.random() * (i + 1)); c.insertBefore(opts[i], opts[j]); var t = opts[i]; opts[i] = opts[j]; opts[j] = t; }
    };
    mcqs.forEach(function (c) {
      shuffleOpts(c);
      c.addEventListener("click", function (e) {
        var b = e.target.closest("button.opt");
        if (!b) return;
        setTimeout(function () { // after the page's own handler has marked it
          if (b.classList.contains("right")) {
            var s = load(QK, {}); s[c.id] = b.textContent.slice(0, 60); store(QK, s); updateBadge();
          }
        }, 0);
      });
    });
    // restore earlier correct answers by replaying the click (also re-opens reveals)
    mcqs.forEach(function (c) {
      var savedTxt = doneSet[c.id];
      if (!savedTxt) return;
      var match = qsa("button.opt", c).filter(function (b) { return b.textContent.slice(0, 60) === savedTxt; })[0];
      if (match) match.click();
    });
    updateBadge();
  }

  /* ---------- visualiser: autoplay, random example, arrow keys ---------- */
  var nextB = byId("next"), prevB = byId("prev"), goB = byId("go");
  if (nextB && prevB && goB) {
    var apT = null;
    var apStop = function () { if (apT) { clearInterval(apT); apT = null; playB.textContent = "▶ play"; } };
    var playB = el("button", "ghost", "▶ play"); playB.title = "autoplay";
    prevB.parentNode.insertBefore(playB, prevB);
    playB.onclick = function () {
      if (apT) { apStop(); return; }
      if (nextB.disabled) goB.click();
      playB.textContent = "⏸ pause";
      apT = setInterval(function () { if (!nextB.disabled) nextB.click(); else apStop(); }, 1300);
    };
    if (cfg.rand) {
      var randB = el("button", "ghost", "🎲 random"); randB.title = "try a random example";
      goB.parentNode.insertBefore(randB, goB.nextSibling);
      randB.onclick = function () { apStop(); cfg.rand(); goB.click(); };
    }
    var hint = el("span", "small", "(or use ← → keys)"); hint.style.fontFamily = "var(--ui)";
    nextB.parentNode.insertBefore(hint, nextB.nextSibling);
    [prevB, nextB, goB].forEach(function (b) { b.addEventListener("click", apStop); });
    document.addEventListener("keydown", function (e) {
      if (e.key !== "ArrowLeft" && e.key !== "ArrowRight") return;
      var t = e.target;
      if (t && (t.tagName === "INPUT" || t.tagName === "TEXTAREA" || t.tagName === "SELECT")) return;
      apStop();
      if (e.key === "ArrowRight" && !nextB.disabled) { nextB.click(); e.preventDefault(); }
      if (e.key === "ArrowLeft" && !prevB.disabled) { prevB.click(); e.preventDefault(); }
    });
  }

  /* ---------- worksheet: checker status + Ctrl+Enter ---------- */
  var ws = byId("worksheet");
  if (ws && typeof CHECK_URL !== "undefined") {
    var firstCell = qs(".wcell");
    var banner = el("div", "chkbanner", "checking for the Lean checker…");
    ws.parentNode.insertBefore(banner, ws);
    (function () {
      var ctl = new AbortController(); setTimeout(function () { ctl.abort(); }, 4000);
      fetch(CHECK_URL, {
        method: "POST", headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ exercise: firstCell ? firstCell.dataset.ex : "", code: "" }), signal: ctl.signal
      }).then(function (r) { return r.json(); }).then(function () {
        banner.className = "chkbanner on";
        banner.innerHTML = "✓ checker online — <b>Run</b> will compile your answers with Lean.";
      }).catch(function () {
        banner.className = "chkbanner off";
        banner.innerHTML = "⚠ checker not running — <b>Run</b> needs it (see <code>web/checker/README.md</code>). " +
          "You can still attempt every cell and compare against its <em>reference solution</em>.";
      });
    })();
    qsa(".wcell textarea").forEach(function (ta) {
      ta.addEventListener("keydown", function (e) {
        if ((e.ctrlKey || e.metaKey) && e.key === "Enter" && typeof runCell === "function") { e.preventDefault(); runCell(ta.closest(".wcell")); }
      });
    });
  }

  /* ---------- proof: collapsible layers (last layer starts folded) ---------- */
  if (cfg.proofSel) {
    var box = qs(cfg.proofSel);
    if (box && qs(".pstep", box) && !qs(".ideas", box)) {   // skip when the proof already uses the idea+dropdown format
      var kids = qsa(cfg.proofSel + " > *").concat(); // element children in order
      kids = Array.prototype.slice.call(box.children);
      var groups = [], g = null;
      kids.forEach(function (n) {
        if (n.classList && n.classList.contains("pstep")) { g = { head: n, rest: [] }; groups.push(g); }
        else if (g) g.rest.push(n);
      });
      if (groups.length > 1) {
        groups.forEach(function (grp) {
          var det = el("details", "layer");   // full proofs collapsed by default — present, one click away
          var sm = document.createElement("summary");
          box.insertBefore(det, grp.head);
          sm.appendChild(grp.head); det.appendChild(sm);
          grp.rest.forEach(function (n) { det.appendChild(n); });
        });
        var first = qs("details.layer", box);
        if (first) first.querySelector("summary").insertAdjacentHTML("beforeend",
          ' <span class="small" style="font-family:var(--ui)">— click to unfold the full proof</span>');
      }
    }
  }
})();
