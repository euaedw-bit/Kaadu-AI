// Histórico de pedras guardado no celular (até 1 ano), em formato compacto.
// Cada "bloco" é uma sequência contínua de pedras:
//   s = 1 letra por pedra (0 a e, em hexadecimal)
//   d = 1 letra por intervalo entre pedras, em segundos (guarda o horário exato de cada pedra)
// Blocos antigos (sem d) continuam funcionando, com horário aproximado.
const DIA = 86400000;
const MAX_DIAS = 365;
const ymd = (t) => { const d = new Date(t); return d.getFullYear() * 10000 + (d.getMonth() + 1) * 100 + d.getDate(); };
const seg = (t) => Math.round(t / 1000);

export function criarHistorico(store, tag) {
  let blocos = []; // { t0, t1, s, d? }
  let versao = 0;
  let cache = { v: -1, flat: '', idx: [] };
  const memo = new WeakMap(); // horários exatos de cada bloco (não é salvo)
  const chave = (dia) => `${tag}:d:${dia}`;

  // horários (ms) de todas as pedras do bloco
  function tempos(b) {
    let m = memo.get(b);
    if (m && m.len === b.s.length) return m.t;
    const t = [];
    if (typeof b.d === 'string' && b.d.length === b.s.length - 1) {
      let s0 = seg(b.t0);
      t.push(s0 * 1000);
      for (let i = 0; i < b.d.length; i++) { s0 += b.d.charCodeAt(i) - 48; t.push(s0 * 1000); }
    } else {
      const n = b.s.length;
      for (let k = 0; k < n; k++) t.push(n <= 1 ? b.t0 : b.t0 + ((b.t1 - b.t0) * k) / (n - 1));
    }
    memo.set(b, { len: b.s.length, t });
    return t;
  }
  const tempoDe = (b, k) => tempos(b)[k];

  function carregar(agora = Date.now(), dias = MAX_DIAS) {
    blocos = [];
    for (let i = dias; i >= 0; i--) {
      const lista = store.get(chave(ymd(agora - i * DIA)), null);
      if (lista) blocos.push(...lista);
    }
    blocos.sort((a, b) => a.t0 - b.t0);
    versao++;
  }

  function gravarDia(dia) {
    store.set(chave(dia), blocos.filter((b) => ymd(b.t0) === dia));
  }

  function juntar(st) { // devolve true se entrou
    const c = st.n.toString(16);
    const ult = blocos[blocos.length - 1];
    if (ult && st.t <= ult.t1) return false; // pedra repetida
    if (ult && typeof ult.d === 'string' && st.t - ult.t1 <= 75000) {
      ult.s += c;
      ult.d += String.fromCharCode(48 + Math.max(0, seg(st.t) - seg(ult.t1)));
      ult.t1 = st.t;
    } else {
      blocos.push({ t0: st.t, t1: st.t, s: c, d: '' });
    }
    return true;
  }

  function adicionar(st) {
    if (!juntar(st)) return;
    versao++;
    gravarDia(ymd(blocos[blocos.length - 1].t0));
  }

  // horários dos brancos desde tMin
  function brancosDesde(tMin) {
    const out = [];
    for (let i = blocos.length - 1; i >= 0; i--) {
      const b = blocos[i];
      if (b.t1 < tMin) break;
      const T = tempos(b);
      for (let k = 0; k < b.s.length; k++) {
        if (b.s[k] === '0' && T[k] >= tMin) out.push(T[k]);
      }
    }
    return out.sort((a, b) => a - b);
  }

  // todas as pedras com t0 <= horário < t1, da mais antiga para a mais nova
  function pedrasEntre(t0, t1) {
    const out = [];
    for (let i = blocos.length - 1; i >= 0; i--) {
      const b = blocos[i];
      if (b.t1 < t0) break;
      if (b.t0 >= t1) continue;
      const T = tempos(b);
      for (let k = 0; k < b.s.length; k++) {
        if (T[k] >= t0 && T[k] < t1) out.push({ n: parseInt(b.s[k], 16), t: T[k] });
      }
    }
    return out.sort((a, b) => a.t - b.t);
  }

  function total() { return blocos.reduce((a, b) => a + b.s.length, 0); }
  function primeira() { return blocos.length ? blocos[0].t0 : 0; }
  function ultima() { return blocos.length ? blocos[blocos.length - 1].t1 : 0; }

  function montar() {
    if (cache.v === versao) return cache;
    let flat = '';
    const idx = [];
    for (const b of blocos) {
      idx.push(flat.length);
      flat += b.s.replace(/[89a-e]/g, 'B').replace(/[1-7]/g, 'R').replace(/0/g, 'W') + '|';
    }
    cache = { v: versao, flat, idx };
    return cache;
  }

  // procura o padrão (ex.: "RRBBR") seguido de branco. Devolve quantas vezes e quando foi a última.
  function buscar(padrao) {
    const { flat, idx } = montar();
    const alvo = padrao + 'W';
    let count = 0;
    let pos = flat.indexOf(alvo);
    while (pos !== -1 && count < 500) { count++; pos = flat.indexOf(alvo, pos + 1); }
    if (!count) return { count: 0, total: 0, quando: null };
    let totalP = 0;
    pos = flat.indexOf(padrao);
    while (pos !== -1 && totalP < 100000) {
      const nx = flat[pos + padrao.length];
      if (nx !== undefined && nx !== '|') totalP++;
      pos = flat.indexOf(padrao, pos + 1);
    }
    const ult = flat.lastIndexOf(alvo) + padrao.length; // posição do branco
    let lo = 0, hi = idx.length - 1;
    while (lo < hi) { const m = (lo + hi + 1) >> 1; if (idx[m] <= ult) lo = m; else hi = m - 1; }
    return { count, total: totalP, quando: tempoDe(blocos[lo], ult - idx[lo]) };
  }

  /* ---------- exportar / importar / limpar ---------- */
  function exportar() {
    return JSON.stringify({ app: 'blaze-historico', v: 2, quando: Date.now(), blocos });
  }

  // junta pedras [{n,t}] com o que já existe, sem duplicar (compara por segundo). Devolve quantas entraram.
  function mesclar(novas) {
    if (!novas || !novas.length) return 0;
    const todas = new Map();
    const colher = (bs) => {
      for (const b of bs) {
        if (!b || typeof b.s !== 'string' || !Number.isFinite(b.t0) || !Number.isFinite(b.t1)) continue;
        const T = tempos({ t0: b.t0, t1: b.t1, s: b.s, d: typeof b.d === 'string' ? b.d : '' });
        for (let k = 0; k < b.s.length; k++) {
          const n = parseInt(b.s[k], 16);
          if (!(n >= 0 && n <= 14)) continue;
          const s = seg(T[k]);
          if (!todas.has(s)) todas.set(s, { n, t: T[k] });
        }
      }
    };
    const antes = total();
    colher(blocos);
    let minNovo = Infinity, maxNovo = 0;
    for (const p of novas) {
      if (!p || !(p.n >= 0 && p.n <= 14) || !Number.isFinite(p.t)) continue;
      const s = seg(p.t);
      if (!todas.has(s)) { todas.set(s, { n: p.n, t: p.t }); minNovo = Math.min(minNovo, p.t); maxNovo = Math.max(maxNovo, p.t); }
    }
    if (minNovo === Infinity) return 0;
    const corte = Date.now() - (MAX_DIAS + 1) * DIA;
    const ord = [...todas.values()].filter((p) => p.t >= corte).sort((a, b) => a.t - b.t);
    blocos = [];
    for (const p of ord) juntar(p);
    // grava só os dias mexidos (e os vizinhos, porque um bloco pode atravessar a meia-noite)
    const dias = new Set(blocos.map((b) => ymd(b.t0)));
    for (let t = minNovo - DIA; t <= maxNovo + DIA; t += DIA) { const d = ymd(t); if (dias.has(d)) gravarDia(d); else store.set(chave(d), null); }
    versao++;
    return Math.max(0, total() - antes);
  }

  // junta o arquivo exportado com o que já existe (sem duplicar). Devolve quantas pedras novas entraram.
  function importar(texto) {
    let obj;
    try { obj = JSON.parse(String(texto).trim()); } catch (e) { throw new Error('O texto colado não é um histórico válido.'); }
    const lista = Array.isArray(obj) ? obj : obj && obj.blocos;
    if (!Array.isArray(lista)) throw new Error('Não encontrei pedras nesse arquivo.');
    const stones = [];
    for (const b of lista) {
      if (!b || typeof b.s !== 'string' || !Number.isFinite(b.t0) || !Number.isFinite(b.t1)) continue;
      const T = tempos({ t0: b.t0, t1: b.t1, s: b.s, d: typeof b.d === 'string' ? b.d : '' });
      for (let k = 0; k < b.s.length; k++) stones.push({ n: parseInt(b.s[k], 16), t: T[k] });
    }
    return mesclar(stones);
  }

  function limpar(agora = Date.now()) {
    for (let i = MAX_DIAS + 1; i >= 0; i--) store.set(chave(ymd(agora - i * DIA)), null);
    blocos = [];
    versao++;
  }

  return { carregar, adicionar, brancosDesde, buscar, pedrasEntre, total, primeira, ultima, exportar, importar, mesclar, limpar };
}
