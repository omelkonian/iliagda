const DATA = (() => {
  const el = document.getElementById("facts");
  if (!el) return null;
  const by = new Map();
  for (const v of JSON.parse(el.textContent).verses) by.set(v.n, v.s);
  return by;
})();

const esc = s => s.replace(/&/g, "&amp;").replace(/</g, "&lt;");

const g = s => `<span class="g">${esc(s)}</span>`;
const QTY = { L: "long", S: "short" };

const QUOTES = (() => {
  const el = document.getElementById("quotes");
  try { return el ? JSON.parse(el.textContent) : {}; } catch (e) { return {}; }
})();

const AGDA_BASE = (document.body.dataset.root || "") + "agda/";
const L1 = "Iliagda.Prosody.Rules.Level1", L2 = "Iliagda.Prosody.Rules.Level2";
const L3 = "Iliagda.Prosody.Rules.Level3", L4 = "Iliagda.Prosody.Rules.Level4";
const AGDA = {
  unwritten:     ["Iliagda.Reading", "Edit.unwritten"],
  longByNature:  [L1, "\u2223Sy-Q\u2223._~\u2032_.longByNature"],
  shortByNature: [L1, "\u2223Sy-Q\u2223._~\u2032_.shortByNature"],
  byLexicon:     [L2, "_~L_.byLexicon"],
  "1160":        [L2, "_\u22A8_~%\u2032_.[1160]"],
  "1161":        [L2, "_\u22A8_~%\u2032_.[1161]"],
  "1162":        [L2, "_\u22A8_~%\u2032_.[1162]"],
  "1163":        [L2, "_\u22A8_~%\u2032_.[1163]"],
  "522":         [L3, "QuantityRules._~\u2217_.[522]"],
  "1173":        [L3, "QuantityRules._~\u2217_.[1173]"],
  "524":         [L3, "QuantityRules._~\u2217_.[524]"],
  "1168":        [L4, "_\u02E2~\u1D50_.[1168]"],
  "1167a":       [L4, "_\u02E2~\u1D50_.[1167/1a]"],
  "1167b":       [L4, "_\u02E2~\u1D50_.[1167/1b]"],
  merge:         ["Iliagda.Prosody.Synizesis", "_-synizizes*-_._∺_"],
  "1184":        [L4, "∣Complies-MQs-HM∣._~′_.reify"],
};
const agdaUrl = r => {
  const t = AGDA[r];
  return t ? `${AGDA_BASE}${t[0]}.html#${encodeURIComponent(t[1])}` : null;
};

const greek = s => s.replace(/[\u0370-\u03FF\u1F00-\u1FFF]+/g,
  m => `<span class="g">${m}</span>`);

const wordOf = (sc, i) => {
  let k = 0;
  for (const n of sc.w) {
    if (i < k + n) return sc.syl.slice(k, k + n).join("");
    k += n;
  }
  throw new Error("no word contains syllable " + i);
};

const subject = (sc, f) => {
  if (f.r === "merge") return f.a[0] + f.a[1];
  const m = sc.f.find(x => x.r === "merge" && (x.i === f.i || x.i === f.i + 1));
  return m ? m.a[0] + m.a[1] : sc.syl[f.i];
};

const NAMES_WORD = new Set(["unwritten", "1160", "1161", "1162", "1163"]);

const me = (sc, f) => {
  const s = subject(sc, f);
  if (NAMES_WORD.has(f.r)) return g(s);
  const w = wordOf(sc, f.i);
  return sc.syl.filter(x => x === s).length > 1 && w !== s
    ? `${g(s)} of ${g(w)}` : g(s);
};

const its = (sc, f, v) => subject(sc, f) === v ? "it " : `its ${g(v)} `;

const closedInWord = f =>
  f.r === "522" && (f.a[1] === "doubleConsonant" || f.a[4] !== "nextWord");

const at = (sc, i, p) => sc.f.some(f => f.i === i && p(f));

const suppressed = (sc, f) =>
  f.q === "S" && at(sc, f.i, closedInWord) && !at(sc, f.i, x => x.r === "524");

let NUM = null;
const ref = k => `<a class="pt" data-k="${k}">(${NUM ? NUM.get(k) : k + 1})</a>`;
const cite = f => f.ref === undefined ? "" : " " + ref(f.ref);

const despite = (sc, fs, f, q) => {
  const prior = f.ref === undefined ? null : fs[f.ref];
  return prior && prior.q && prior.q !== q
    ? `${me(sc, f)} would be ${QTY[prior.q]} ${ref(f.ref)}, but`
    : me(sc, f);
};

const turns = (fs, f) => {
  const prior = f.ref === undefined ? null : fs[f.ref];
  return !prior || !prior.q ? "is" : prior.q === f.q ? "remains" : "turns";
};

const REACH = { within: "", nextSyllable: " in the next syllable", nextWord: " of the following word" };
const ORDINAL = { 1: "first", 2: "second", 3: "third", 4: "fourth", 5: "fifth", 6: "sixth" };

const RULES = {
  unwritten: (sc, f) => ["526",
    `${g(f.a[2])} is read ${g(wordOf(sc, f.i))}: its ${g(f.a[0])} is not written.`],

  longByNature: (sc, f) => {
    const [kind, x, y] = f.a;
    if (kind === "diphthong")
      return ["521", `${me(sc, f)} is long by nature: it contains the diphthong ${g(x + y)}.`];
    if (kind === "longVowel")
      return ["519", `${me(sc, f)} is long by nature: it contains the long vowel ${g(x)}.`];
    return ["537", `${me(sc, f)} is long by nature: ${its(sc, f, x)}bears a circumflex.`];
  },

  shortByNature: (sc, f) => ["519",
    `${me(sc, f)} is short: ${its(sc, f, f.a[0])}is short by nature.`],

  byLexicon: (sc, f) => ["519",
    `${me(sc, f)} is ${QTY[f.a[0]]}: the vocabulary fixes the doubtful vowel of ${g(f.a[1])}`
    + (f.a[2] === "stem" ? ", matched as a stem." : ".")],

  "1160": (sc, f) => ["545",
    `${me(sc, f)} is short: it is the ultima of ${g(wordOf(sc, f.i))}, whose penult `
    + `${g(f.a[1])} bears the circumflex.`],

  "1161": (sc, f) => ["1161",
    `${me(sc, f)} is long: it is the ultima of ${g(wordOf(sc, f.i))}, whose penult `
    + `${g(f.a[1])} is long${cite(f)} and bears the acute.`],

  "1162": (sc, f) => ["1162",
    `${me(sc, f)} is short: it is the penult of ${g(wordOf(sc, f.i))}, bearing the acute `
    + `while the ultima ${g(f.a[1])} is short${cite(f)}.`],

  "1163": (sc, f) => ["544",
    `${me(sc, f)} is short: it is the ultima of ${g(wordOf(sc, f.i))}, whose antepenult `
    + `${g(f.a[1])} bears the accent.`],

  merge: (sc, f) => ["586",
    `${g(f.a[0])} and ${g(f.a[1])} are read as the one syllable ${g(subject(sc, f))}`
    + (f.a[2] ? ", across the word boundary" : "") + ", which counts long."],

  "1173": (sc, f) => ["1173",
    `${me(sc, f)} may be shortened: its ${g(f.a[1])} stands before vowel-initial `
    + `${g(f.a[2])}${f.a[3] ? " of the following word" : ""}; here it `
    + `${turns(sc.f, f)} ${QTY[f.a[0]]}${cite(f)}.`],

  "524": (sc, f) => ["524",
    `${me(sc, f)} is common: its ${g(f.a[1])} is a short vowel standing before the mute `
    + `${g(f.a[2])} and the ${f.a[4] ? "nasal" : "liquid"} ${g(f.a[3])} in the same word; `
    + `here it ${turns(sc.f, f)} ${QTY[f.a[0]]}${cite(f)}.`],
};

const SUPERSEDES = {
  "522": (sc, fs, f) => ["522",
    (closedInWord(f)
      ? `${me(sc, f)} is long by position: its ${g(f.a[0])} is followed by `
      : `${despite(sc, fs, f, "L")} is long: its ${g(f.a[0])} is followed by `)
    + (f.a[1] === "doubleConsonant"
        ? `the double consonant ${g(f.a[2])}.`
        : `${g(f.a[2])} and ${g(f.a[3])}${REACH[f.a[4]]}.`)],

  "1168": (sc, fs, f) => ["1168",
    `${despite(sc, fs, f, "L")} is lengthened in thesis: it ends in ${g(f.a[0] + f.a[1])} `
    + `before vowel-initial ${g(f.a[2])}.`],

  "1167a": (sc, fs, f) => ["1167",
    `${despite(sc, fs, f, "L")} counts long: its word ends at the caesura, whose pause `
    + `fills out the time required.`],

  "1167b": (sc, fs, f) => ["1167",
    `${despite(sc, fs, f, "L")} counts long: its word ends here, closing the `
    + `${ORDINAL[f.a[0]] || f.a[0] + "th"} foot as a spondee.`],

  "1184": (sc, fs, f) => ["1184",
    `${despite(sc, fs, f, "L")} counts long: it is the last syllable of the verse.`],
};

const sentence = (sc, fs, f) => {
  if (SUPERSEDES[f.r]) return SUPERSEDES[f.r](sc, fs, f);
  const rule = RULES[f.r];
  if (!rule) return [null, null];
  return rule(sc, f);
};

const unexplained = sc => {
  const merges = new Set(sc.f.filter(f => f.r === "merge").map(f => f.i));
  const stated = new Set(sc.f.map(f => f.i));
  const out = [];
  let k = 0;
  for (let i = 0; i < sc.syl.length; i++, k++) {
    if (merges.has(i + 1)) { i++; continue; }
    if (!stated.has(i)) out.push({ syl: sc.syl[i], q: sc.q[k], i });
  }
  return out;
};

function renderArgument(ol) {
  if (ol.dataset.done) return;
  const sc = DATA.get(+ol.dataset.v)[+ol.dataset.r];
  const keep = sc.f.map((f, k) => k).filter(k => !suppressed(sc, sc.f[k]));
  NUM = new Map(keep.map((k, i) => [k, i + 1]));
  const points = keep.map(k => {
    const f = sc.f[k];
    const [pharr, text] = sentence(sc, sc.f, f);
    return text === null
      ? `<li class="err" data-k="${k}">unknown rule: ${esc(f.r)}</li>`
      : `<li data-k="${k}" data-i="${f.i}">${text}`
        + `<span class="pharr" data-a="${pharr}" data-r="${esc(f.r)}">${pharr}</span></li>`;
  });

  for (const u of unexplained(sc))
    points.push(`<li data-i="${u.i}">${me(sc, { r: "", i: u.i })} must be ${QTY[u.q]} `
      + `to complete the metre.`
      + `<span class="pharr" data-a="1169">1169</span></li>`);
  ol.innerHTML = points.join("");
  ol.dataset.done = "1";
}

let openVerse = null;

document.querySelectorAll(".vtext").forEach(t => {
  t.addEventListener("click", () => {
    if (!getSelection().isCollapsed) return;
    const verse = t.closest(".verse");
    const ol = verse.querySelector(".varg.on");
    if (!ol) return;
    const closing = openVerse === verse;
    if (openVerse) openVerse.classList.remove("open");
    openVerse = null;
    if (closing) return;
    renderArgument(ol);
    verse.classList.add("open");
    openVerse = verse;
  });
});

const tokenFor = (verse, i) => {
  for (const s of verse.querySelectorAll(".vtext.on .syl")) {
    const a = +s.dataset.i, n = +(s.dataset.n || 1);
    if (i >= a && i < a + n) return s;
  }
  return null;
};

let lit = [];
const clearLit = () => { for (const e of lit) e.classList.remove("lit"); lit = []; };
const light = e => { if (e) { e.classList.add("lit"); lit.push(e); } };

const hover = e => {
  const li = e.target.closest(".varg li"), pt = e.target.closest("a.pt");
  if (!li && !pt) { if (lit.length) clearLit(); return; }
  clearLit();
  if (pt) light(pt.closest(".varg").querySelector(`li[data-k="${pt.dataset.k}"]`));
  if (li && li.dataset.i !== undefined)
    light(tokenFor(li.closest(".verse"), +li.dataset.i));
};
document.addEventListener("mouseover", hover);

let pop = null;
const closePop = () => { if (pop) { pop.remove(); pop = null; } };

document.addEventListener("click", e => {
  const ref = e.target.closest(".pharr");
  if (e.target.closest(".pop")) return;
  const same = pop && ref && pop.parentElement === ref;
  closePop();
  if (!ref || same) return;

  const quote = QUOTES[ref.dataset.a];
  const url = ref.dataset.r ? agdaUrl(ref.dataset.r) : null;
  pop = document.createElement("span");
  pop.className = "pop";
  pop.innerHTML =
    (quote ? `<span class="pop-text">${greek(esc(quote))}</span>`
             : `<span class="pop-text none">not yet written</span>`)
    + (url ? `<a class="pop-agda" href="${url}" target="_blank" rel="noopener">`
             + `in Agda \u2197</a>` : "");
  ref.appendChild(pop);

  const box = pop.getBoundingClientRect();
  if (box.right > innerWidth - 8) pop.style.left = `${innerWidth - 8 - box.right}px`;
});

addEventListener("keydown", e => { if (e.key === "Escape") closePop(); });

document.querySelectorAll(".vside a[data-r]").forEach(a => {
  a.addEventListener("click", () => {
    const verse = a.closest(".verse");
    verse.querySelectorAll(".vside a").forEach(x => x.classList.toggle("on", x === a));
    verse.querySelectorAll(".vtext, .varg").forEach(t =>
      t.classList.toggle("on", t.dataset.r === a.dataset.r));
    const ol = verse.querySelector(".varg.on");
    if (ol && verse.classList.contains("open")) renderArgument(ol);
  });
});
