// CÉREBRO: roda dentro do app. Observa as pedras, mede as circunstâncias do gráfico,
// testa hipóteses contra o acaso (passado = treino/teste; presente = ao vivo), "chuta" em tempo
// real e conta acertos e erros. Também roda as estratégias (Base 39, PA, BC) e guarda como
// cada uma se sai em cada circunstância. Tudo é guardado no celular.
import { novoEstado, addStone, avancar, hhmm } from './engine';

const MIN = 60000;
export const ALTA_MIN = 10;        // pretas "altas" = 10 a 14
const ALTA_ENTRA = 0.9, ALTA_SAI = 0.7; // por acaso ~71%; liga com 9+ em 10
const GAP_MS = 120000;             // buraco maior que isso entre pedras = app fechado/sem sinal
const MAX_LINHAS = 3000;
const MAX_PEDRAS = 60000;
const REPLAY_ENGINE = 3000;        // quantas pedras recentes passam pelo motor das estratégias ao ligar
const BASE_REP10 = 0.0285;         // chance de acaso de ter só 5 valores diferentes (ou menos) em 10 pedras
const MIN_TREINO = 40;
const MIN_TESTE = 20;
const MIN_VIVO = 30;
const Z_BONF = 3.4;                // exigência alta (muitas hipóteses testadas ao mesmo tempo)
const MAX_CHUTES_ABERTOS = 4;

const pad = (n) => String(n).padStart(2, '0');
const hms = (t) => { const d = new Date(t); return `${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`; };
const dmhms = (t) => { const d = new Date(t); return `${pad(d.getDate())}/${pad(d.getMonth() + 1)} ${hms(t)}`; };
const pc = (x) => `${(x * 100).toFixed(1).replace('.', ',')}%`;
const p0Branco = (k) => 1 - Math.pow(14 / 15, k);
const zsc = (n, h, p) => (n ? (h - n * p) / Math.sqrt(n * p * (1 - p)) : 0);
const NOME_EST = { B39: 'Base 39', PA: 'PA', BC: 'BC' };

/* ---------- hipóteses: condição (o que o gráfico mostra) x alvo (o que se espera depois) ---------- */
function montarHipoteses() {
  const conds = [];
  const alvosB = [{ tipo: 'branco', k: 2 }, { tipo: 'branco', k: 4 }, { tipo: 'branco', k: 6 }];
  const add = (id, nome, fn, alvos) => conds.push({ id, nome, fn, alvos });
  for (const v of [8, 9, 10, 11, 12, 13, 14]) {
    add(`u${v}`, `depois de um ${v}`, (f) => f.n === v, alvosB);
    add(`u${v}r1`, `depois de um ${v} com repetição`, (f) => f.n === v && f.rep, alvosB);
    add(`u${v}r2`, `depois de um ${v} com pretas altas`, (f) => f.n === v && f.altasReg, alvosB);
    add(`u${v}r3`, `depois de um ${v} em regime (repetição + pretas altas)`, (f) => f.n === v && f.reg3, alvosB);
  }
  add('r1', 'em repetição (poucos valores diferentes)', (f) => f.rep, alvosB);
  add('r2', 'em pretas altas', (f) => f.altasReg, alvosB);
  add('r3', 'em regime (repetição + pretas altas)', (f) => f.reg3, alvosB);
  for (const m of [20, 30, 40, 49]) add(`s${m}`, `seca de ${m}+ min sem branco`, (f) => f.n !== 0 && f.secaMin !== null && f.secaMin >= m, alvosB);
  add('col', 'dois brancos colados', (f) => f.colados, [...alvosB, { tipo: 'rep10' }]);
  add('solo', 'branco isolado (controle)', (f) => f.brancoSolo, [{ tipo: 'rep10' }]);
  add('fimSolo', 'fim de seca (30+ min) com 1 branco só', (f) => f.soloFim, [{ tipo: 'branco', k: 20 }]);
  add('fimDupla', 'fim de seca (30+ min) com 2 brancos colados', (f) => f.duplaFim, [{ tipo: 'branco', k: 20 }]);
  const hs = [];
  for (const c of conds) {
    for (const a of c.alvos) {
      const k = a.tipo === 'branco' ? a.k : 10;
      hs.push({
        id: a.tipo === 'branco' ? `${c.id}_b${k}` : `${c.id}_rep10`,
        nome: a.tipo === 'branco' ? `${c.nome} → branco em até ${k} pedras` : `${c.nome} → repetição alta nas 10 pedras seguintes`,
        cond: c.fn, alvo: a, need: k,
        p0: a.tipo === 'branco' ? p0Branco(k) : BASE_REP10,
        fases: { treino: { n: 0, h: 0 }, teste: { n: 0, h: 0 }, vivo: { n: 0, h: 0 } },
        pend: null,
      });
    }
  }
  return hs;
}

export function criarCerebro({ store, tag = 'cerebro' }) {
  const KEY = `${tag}:estado`;
  const H = [];        // pedras {n,t}
  const SEG = [];      // início do trecho contínuo de cada pedra
  const HIP = montarHipoteses();
  const HIDX = {};
  HIP.forEach((h) => { HIDX[h.id] = h; });
  let LINHAS = [];
  let seqLinha = 0;
  let seqChute = 0;
  let silencio = true;
  let pronto = false;
  let fila = [];
  let sujo = false;
  let fAtual = null;
  let chutesAbertos = 0;
  let placar = { n: 0, h: 0, esp: 0 };
  let ST = { vivo: {}, hist: {} };   // desempenho das estratégias por circunstância
  let ultResumo = Date.now();
  let eng = novoEstado();
  const EST_MIN = new Map(); let ENG_T0 = 0; let engReg = 0;
  const ouvintes = new Set();
  const flags = { rep: false, altas: false, reg: false, ult: {} };
  let secaMarcas = new Set();
  let carregadas = 0;

  /* ---------- guardar / carregar ---------- */
  function carregarEstado() {
    const o = store.get(KEY, null);
    if (!o || o.v !== 1) return;
    LINHAS = Array.isArray(o.linhas) ? o.linhas : [];
    seqLinha = o.seqLinha || LINHAS.reduce((a, l) => Math.max(a, l.id), 0);
    seqChute = o.seqChute || 0;
    placar = o.placar || placar;
    ST.vivo = o.stVivo || {};
    ultResumo = o.ultResumo || Date.now();
    for (const id in o.vivo || {}) if (HIDX[id]) HIDX[id].fases.vivo = o.vivo[id];
  }
  function salvar(forcar = false) {
    if (!sujo && !forcar) return;
    const vivo = {};
    HIP.forEach((h) => { if (h.fases.vivo.n) vivo[h.id] = h.fases.vivo; });
    store.set(KEY, { v: 1, seqLinha, seqChute, placar, stVivo: ST.vivo, ultResumo, vivo, linhas: LINHAS.slice(-MAX_LINHAS) });
    sujo = false;
  }

  function emitir(tipo, txt, t = Date.now()) {
    if (silencio) return;
    const l = { id: ++seqLinha, t, tipo, txt };
    LINHAS.push(l);
    if (LINHAS.length > MAX_LINHAS) LINHAS.shift();
    sujo = true;
    ouvintes.forEach((fn) => { try { fn(l); } catch (e) {} });
  }
  const sempre = (tipo, txt) => { const s = silencio; silencio = false; emitir(tipo, txt); silencio = s; };

  /* ---------- sensores: o que o gráfico está mostrando ---------- */
  function feat(i) {
    const s = SEG[i];
    const n = H[i].n, t = H[i].t;
    const f = { n, t, i };
    if (i - s >= 9) { const set = new Set(); for (let j = i - 9; j <= i; j++) set.add(H[j].n); f.dist = set.size; } else f.dist = null;
    let pr = 0, al = 0;
    for (let j = i; j >= s && i - j < 40 && pr < 10; j--) { const v = H[j].n; if (v >= 8) { pr++; if (v >= ALTA_MIN) al++; } }
    f.pretas = pr; f.altas = al; f.prop = pr >= 6 ? al / pr : null;
    let k = i;
    while (k >= s && H[k].n !== 0) k--;
    f.secaMin = k >= s ? (t - H[k].t) / MIN : null;
    f.secaPed = k >= s ? i - k : null;
    const gapAntes = (w) => { let p = w - 1; while (p >= s && H[p].n !== 0) p--; return p >= s ? (H[w].t - H[p].t) / MIN : null; };
    f.colados = n === 0 && i - 1 >= s && H[i - 1].n === 0;
    f.brancoSolo = false; f.soloFim = false; f.duplaFim = false;
    if (n !== 0 && i - 1 >= s && H[i - 1].n === 0) {
      const isolado = !(i - 2 >= s && H[i - 2].n === 0);
      f.brancoSolo = isolado;
      if (isolado) { const g = gapAntes(i - 1); f.soloFim = g !== null && g >= 30; }
    }
    if (f.colados) {
      const w = i - 1;
      const isolado0 = !(w - 1 >= s && H[w - 1].n === 0);
      if (isolado0) { const g = gapAntes(w); f.duplaFim = g !== null && g >= 30; }
    }
    f.rep = f.dist !== null && f.dist <= 5;
    f.altasReg = f.prop !== null && f.prop >= ALTA_ENTRA;
    f.reg3 = f.rep && f.altasReg;
    return f;
  }

  function status(h) {
    const tr = h.fases.treino, te = h.fases.teste, vv = h.fases.vivo;
    const zt = zsc(tr.n, tr.h, h.p0), ze = zsc(te.n, te.h, h.p0), zv = zsc(vv.n, vv.h, h.p0);
    if (vv.n >= MIN_VIVO && Math.abs(zv) >= 1.96 && Math.sign(zv) === Math.sign(zt) && Math.abs(zt) >= Z_BONF) return 'confirmada';
    if (tr.n >= MIN_TREINO && Math.abs(zt) >= Z_BONF && te.n >= MIN_TESTE && Math.abs(ze) >= 1.64 && Math.sign(ze) === Math.sign(zt)) return 'promissora';
    if (tr.n >= MIN_TREINO && Math.abs(zt) >= 2.5) return 'observar';
    return 'sem evidência';
  }
  const taxa = (c) => (c.n ? c.h / c.n : 0);

  /* ---------- um passo: uma pedra nova ---------- */
  function passo(i, fase) {
    const f = feat(i);
    fAtual = f;
    for (const h of HIP) {
      const pd = h.pend;
      if (!pd) continue;
      if (SEG[i] !== SEG[pd.i0]) { if (pd.chute) { chutesAbertos = Math.max(0, chutesAbertos - 1); emitir('info', `Chute #${pd.chute} cancelado (houve um buraco nas pedras).`, f.t); } h.pend = null; continue; }
      if (i - pd.i0 >= h.need) {
        let hit;
        if (h.alvo.tipo === 'branco') { hit = false; for (let j = pd.i0 + 1; j <= i; j++) if (H[j].n === 0) { hit = true; break; } }
        else { const set = new Set(); for (let j = pd.i0 + 1; j <= pd.i0 + 10; j++) set.add(H[j].n); hit = set.size <= 5; }
        const c = h.fases[pd.fase]; c.n++; if (hit) c.h++;
        h.pend = null;
        if (pd.chute) {
          chutesAbertos = Math.max(0, chutesAbertos - 1);
          placar.n++; if (hit) placar.h++; placar.esp += h.p0;
          emitir(hit ? 'ok' : 'erro', `${hit ? '✅' : '❌'} Chute #${pd.chute} ${hit ? 'ACERTOU' : 'errou'}: ${h.nome}. Placar dos chutes: ${placar.h} de ${placar.n} (por acaso seria ~${(placar.esp).toFixed(1).replace('.', ',')}).`, f.t);
          sujo = true;
        }
        if (fase === 'vivo') sujo = true;
      }
    }
    for (const h of HIP) {
      if (h.pend || !h.cond(f)) continue;
      h.pend = { i0: i, fase, chute: null };
      if (fase === 'vivo') avaliarChute(h, f);
    }
    return f;
  }

  function avaliarChute(h, f) {
    if (chutesAbertos >= MAX_CHUTES_ABERTOS) return;
    const st = status(h);
    if (st === 'sem evidência') return;
    const zt = zsc(h.fases.treino.n, h.fases.treino.h, h.p0);
    if (zt <= 0) return; // só chuta quando o passado mostrou MAIS que o acaso
    const tr = h.fases.treino;
    h.pend.chute = ++seqChute;
    chutesAbertos++;
    const alvo = h.alvo.tipo === 'branco' ? `branco em até ${h.need} pedras` : 'repetição alta (≤5 valores diferentes) nas próximas 10 pedras';
    emitir('chute', `🎯 Chute #${h.pend.chute} [${st}]: ${h.nome.split(' → ')[0]} → espera ${alvo}. No passado: ${pc(taxa(tr))} contra ${pc(h.p0)} do acaso (${tr.n} casos).`, f.t);
  }

  /* ---------- aprendiz de regime: descobre SOZINHO quando "repetição" e "pretas altas" existem de verdade ---------- */
  // Ideia: se o gráfico tem fases (repetitiva / não repetitiva), então estar nela agora torna MAIS provável
  // continuar nela na janela seguinte (janelas separadas, sem sobreposição). Em sorteio puro isso não acontece.
  const APR = { rep: null, altas: null, tab: { rep: [], altas: [] }, quando: 0, ult: '' };
  const distEm = (i, W) => {
    if (i - SEG[i] < W - 1) return null;
    const c = new Uint8Array(15); let d = 0;
    for (let j = i - W + 1; j <= i; j++) { if (!c[H[j].n]) { c[H[j].n] = 1; d++; } }
    return d;
  };
  const propEm = (i, m, W) => {
    if (i - SEG[i] < W - 1) return null;
    let b = 0, a = 0;
    for (let j = i - W + 1; j <= i; j++) { const v = H[j].n; if (v >= 8) { b++; if (v >= m) a++; } }
    return b >= 6 ? a / b : null;
  };
  function persistencia(arr, W, corte) {
    // arr[i] = 1/0 (no estado ou não) ou -1 (sem dado). Pares (i, i+W) de janelas separadas.
    const fase = (a, b) => {
      let nA = 0, nAB = 0, nB = 0, nT = 0, nE = 0;
      for (let i = a; i + W < b; i += W) {
        const j = i + W;
        if (arr[i] < 0 || arr[j] < 0 || SEG[j] !== SEG[i]) continue;
        nT++; if (arr[j] === 1) nB++; if (arr[i] === 1) { nA++; if (arr[j] === 1) nAB++; }
      }
      const pB = nT ? nB / nT : 0;
      const z = nA >= 15 && pB > 0 && pB < 1 ? (nAB - nA * pB) / Math.sqrt(nA * pB * (1 - pB)) : 0;
      return { nA, nAB, pB, z, pCont: nA ? nAB / nA : 0 };
    };
    const N = arr.length;
    return { tr: fase(W, corte), te: fase(corte, N) };
  }
  function aprenderRegimes() {
    const N = H.length;
    if (N < 600) return;
    const corte = Math.floor(N * 0.7);
    const rep = [], altas = [];
    for (const W of [8, 10, 12, 15, 20]) {
      const esp = 15 * (1 - Math.pow(14 / 15, W));
      const arrD = new Int8Array(N);
      for (let i = 0; i < N; i++) { const d = distEm(i, W); arrD[i] = d === null ? -1 : d; }
      for (const k of [3, 2, 1]) {
        const d = Math.max(2, Math.floor(esp) - k + 1 - 1);
        if (rep.some((c) => c.W === W && c.d === d)) continue;
        const arr = Int8Array.from(arrD, (v) => (v < 0 ? -1 : v <= d ? 1 : 0));
        rep.push({ W, d, esp, ...persistencia(arr, W, corte) });
      }
    }
    for (const m of [10, 11, 12]) {
      const ch = (15 - m) / 7;
      const arrP = new Float32Array(N);
      for (let i = 0; i < N; i++) { const p = propEm(i, m, 20); arrP[i] = p === null ? -1 : p; }
      for (const mais of [0.2, 0.3]) {
        const th = Math.min(1, ch + mais);
        const arr = Int8Array.from(arrP, (v) => (v < 0 ? -1 : v >= th - 1e-9 ? 1 : 0));
        altas.push({ m, th, ch, W: 20, ...persistencia(arr, 20, corte) });
      }
    }
    const melhor = (lst) => lst.slice().sort((a, b) => b.tr.z - a.tr.z)[0];
    const classe = (c) => (!c ? 'não' : c.tr.z >= 3.3 && c.te.z >= 1.64 ? 'existe' : c.tr.z >= 3.3 ? 'talvez' : 'não');
    APR.tab = { rep, altas };
    const br = melhor(rep), ba = melhor(altas);
    br.cls = classe(br); ba.cls = classe(ba);
    APR.rep = br; APR.altas = ba; APR.quando = Date.now();
    const resumoTxt = `rep:${br.W}/${br.d}/${br.cls} altas:${ba.m}/${ba.th.toFixed(2)}/${ba.cls}`;
    if (resumoTxt !== APR.ult) {
      APR.ult = resumoTxt;
      const fr = (c, t) => `${pc(c.pCont)} de continuar (acaso ${pc(c.pB)}; ${c.nA} casos; z=${c.z.toFixed(1)})`;
      sempre('descoberta', `🧬 Repetição: melhor definição que achei = "${br.d} valores diferentes ou menos em ${br.W} pedras". Treino: ${fr(br.tr)}. Teste: ${fr(br.te)}. Veredito: ${br.cls === 'existe' ? 'fases de repetição EXISTEM (passou no treino e no teste)' : br.cls === 'talvez' ? 'talvez exista (só passou no treino)' : 'sem prova de que existam fases; parece sorteio'}.`);
      sempre('descoberta', `🧬 Pretas altas: melhor definição = "${Math.round(ba.th * 100)}% ou mais das pretas são ${ba.m}-14 (por acaso ${pc(ba.ch)})". Treino: ${fr(ba.tr)}. Teste: ${fr(ba.te)}. Veredito: ${ba.cls === 'existe' ? 'fases EXISTEM' : ba.cls === 'talvez' ? 'talvez exista' : 'sem prova de fases; parece sorteio'}.`);
    }
  }
  // definição usada AGORA para dizer "está repetitivo": a aprendida (se tem prova) ou a padrão
  const defRep = () => (APR.rep && APR.rep.cls !== 'não' ? { W: APR.rep.W, d: APR.rep.d, ap: true } : { W: 10, d: 5, ap: false });
  const defAltas = () => (APR.altas && APR.altas.cls !== 'não' ? { m: APR.altas.m, ent: APR.altas.th, sai: Math.max(APR.altas.ch + 0.05, APR.altas.th - 0.15), W: 20, ap: true } : { m: ALTA_MIN, ent: ALTA_ENTRA, sai: ALTA_SAI, W: 10, ap: false });

  /* ---------- OBSERVATÓRIO: as regras que o dono descreveu (dezenas, devedor, dupla/39/49, pedra 5, sinais 11/12) ---------- */
  // Definições do dono:
  //  - dupla = os 2 brancos do MESMO minuto (as duas pedras do minuto). Conta como UM só evento.
  //  - janela dos 39 = minutos M+38 a M+40 (6 pedras); janela dos 49 = minutos M+48 a M+50.
  //  - alerta: pedra 5 vermelha 10 minutos antes do minuto-alvo (M+29 para o 39; M+39 para o 49).
  //  - dezena devedora: dezena (0-9, 10-19...) sem branco na hora anterior. 1 branco quita, mas espera-se (dívida+1).
  const hmin = (mi) => { const d = new Date(mi * MIN); return `${pad(d.getHours())}:${pad(d.getMinutes())}`; };
  const binom = (n, k, p) => { let c = 1; for (let j = 0; j < k; j++) c = (c * (n - j)) / (j + 1); return c * Math.pow(p, k) * Math.pow(1 - p, n - k); };
  const pMais = (n, k, p) => { let a = 0; for (let j = 0; j < k; j++) a += binom(n, j, p); return 1 - a; };
  const ctxEm = (i) => {
    const dr = defRep(), da = defAltas();
    const d = distEm(i, dr.W);
    const pa = da.ap ? propEm(i, da.m, da.W) : feat(i).prop;
    return { rep: d !== null && d <= dr.d, altas: pa !== null && pa >= da.ent };
  };
  const fmtTaxa = (n, h, p0) => (n ? `${pc(h / n)} (${h}/${n}) | acaso ${pc(p0)} | z=${zsc(n, h, p0).toFixed(1)}` : 'sem casos ainda');
  const fmtSub = (n, h) => (n ? `${pc(h / n)} (${h}/${n})` : '—');

  function observatorio() {
    const N = H.length;
    const L = [];
    if (N < 200) { L.push('- poucos dados (precisa de algumas horas de pedras)'); return L; }
    const off = new Date(H[N - 1].t).getTimezoneOffset() * MIN;
    const mm = new Map();
    for (let i = 0; i < N; i++) { const m = Math.floor(H[i].t / MIN); let l = mm.get(m); if (!l) { l = []; mm.set(m, l); } l.push(i); }
    const dentro = (a, b) => { const o = []; for (let m = a; m <= b; m++) { const l = mm.get(m); if (l) for (const x of l) o.push(x); } return o; };
    const ultMin = Math.floor(H[N - 1].t / MIN);

    /* A) brancos por dezena de minuto */
    const slots = new Map();
    for (let i = 0; i < N; i++) {
      const k = Math.floor((H[i].t - off) / (10 * MIN));
      let o = slots.get(k); if (!o) { o = { n: 0, w: 0, i0: i }; slots.set(k, o); }
      o.n++; if (H[i].n === 0) o.w++;
    }
    const kUlt = Math.floor((H[N - 1].t - off) / (10 * MIN));
    const valido = (k) => { const o = slots.get(k); return !!o && o.n >= 18 && k < kUlt; };
    const dist = [0, 0, 0, 0]; const porDez = [0, 1, 2, 3, 4, 5].map(() => ({ n: 0, w: 0 })); let nVal = 0;
    for (const [k, o] of slots) {
      if (!valido(k)) continue;
      nVal++; dist[Math.min(3, o.w)]++;
      const z = ((k % 6) + 6) % 6; porDez[z].n++; porDez[z].w += o.w;
    }
    L.push('A) BRANCOS POR DEZENA DE MINUTO');
    if (nVal) {
      const esp = [binom(20, 0, 1 / 15), binom(20, 1, 1 / 15), binom(20, 2, 1 / 15), pMais(20, 3, 1 / 15)];
      L.push(`   ${nVal} dezenas completas analisadas. Quantidade de brancos: real contra acaso`);
      ['0', '1', '2', '3+'].forEach((nm, j) => L.push(`   ${nm} brancos: ${pc(dist[j] / nVal)} (acaso ${pc(esp[j])})`));
      L.push('   Média de brancos por dezena (acaso 1,33): ' + porDez.map((o, z) => `${z * 10}-${z * 10 + 9}: ${o.n ? (o.w / o.n).toFixed(2).replace('.', ',') : '—'}`).join(' | '));
    } else L.push('   ainda sem dezenas completas');

    /* B) dezena devedora */
    L.push('');
    L.push('B) DEZENA DEVEDORA (mesma dezena nas horas anteriores sem branco)');
    const dev = [0, 1, 2, 3].map(() => ({ n: 0, g1: 0, g2: 0, gd: 0, ctx: { rep1: [0, 0], rep0: [0, 0], al1: [0, 0], al0: [0, 0] } }));
    for (const [k, o] of slots) {
      if (!valido(k) || !valido(k - 6)) continue;
      let d = 0;
      for (let q = 1; q <= 3 && valido(k - 6 * q) && slots.get(k - 6 * q).w === 0; q++) d++;
      const D = dev[d]; D.n++;
      if (o.w >= 1) D.g1++;
      if (o.w >= 2) D.g2++;
      if (d >= 1 && o.w >= d + 1) D.gd++;
      if (d >= 1) {
        const c = ctxEm(o.i0); const ok = o.w >= d + 1 ? 1 : 0;
        const a = c.rep ? D.ctx.rep1 : D.ctx.rep0; a[0]++; a[1] += ok;
        const b = c.altas ? D.ctx.al1 : D.ctx.al0; b[0]++; b[1] += ok;
      }
    }
    dev.forEach((D, d) => {
      L.push(`   Dívida ${d} (${d === 0 ? 'hora anterior pagou' : d + ' hora(s) seguidas sem branco nessa dezena'}): ${D.n} casos`);
      if (!D.n) return;
      L.push(`     pagou 1+ branco: ${fmtTaxa(D.n, D.g1, pMais(20, 1, 1 / 15))}`);
      L.push(`     pagou 2+ brancos: ${fmtTaxa(D.n, D.g2, pMais(20, 2, 1 / 15))}`);
      if (d >= 1) {
        L.push(`     pagou o esperado (${d + 1}+ brancos): ${fmtTaxa(D.n, D.gd, pMais(20, d + 1, 1 / 15))}`);
        L.push(`     esperado respeitado com repetição ${fmtSub(...D.ctx.rep1)} | sem repetição ${fmtSub(...D.ctx.rep0)}`);
        L.push(`     esperado respeitado com pretas altas ${fmtSub(...D.ctx.al1)} | sem ${fmtSub(...D.ctx.al0)}`);
      }
    });

    /* C) dupla -> 39 / 49 */
    const duplas = [];
    for (const [m, l] of mm) if (l.length === 2 && H[l[0]].n === 0 && H[l[1]].n === 0) duplas.push(m);
    duplas.sort((a, b) => a - b);
    const ev = [];
    for (const M of duplas) {
      if (M + 40 > ultMin) continue;
      const w39 = dentro(M + 38, M + 40);
      if (w39.length < 5) continue;
      const e = { M, w39, hit39: w39.some((i) => H[i].n === 0), ctx: ctxEm(w39[0]) };
      if (M + 50 <= ultMin) { const w49 = dentro(M + 48, M + 50); if (w49.length >= 5) { e.w49 = w49; e.hit49 = w49.some((i) => H[i].n === 0); } }
      e.a29 = dentro(M + 29, M + 29).some((i) => H[i].n === 5);
      e.a39 = dentro(M + 39, M + 39).some((i) => H[i].n === 5);
      e.dentroAlerta = dentro(M + 29, M + 29).length >= 2;
      ev.push(e);
    }
    const corteM = ev.length ? ev[Math.floor(ev.length / 2)].M : 0;
    const recente = (e) => e.M >= corteM;
    const cnt = (arr, f) => { let n = 0, h = 0; for (const e of arr) { const r = f(e); if (r === null || r === undefined) continue; n++; if (r) h++; } return [n, h]; };
    const P6 = p0Branco(6);
    const r39 = (e) => e.hit39;
    const r49 = (e) => (!e.hit39 && e.hit49 !== undefined ? e.hit49 : null);
    L.push('');
    L.push('C) DOIS BRANCOS NO MESMO MINUTO -> BRANCO 39 MINUTOS DEPOIS (±1 min), SENÃO 49 MINUTOS DEPOIS (±1 min)');
    L.push(`   Duplas no mesmo minuto encontradas: ${duplas.length} (analisadas com janela completa: ${ev.length})`);
    const c39 = cnt(ev, r39);
    L.push(`   Pagou na janela dos 39 (6 pedras): ${fmtTaxa(c39[0], c39[1], P6)}`);
    L.push(`      metade antiga ${fmtSub(...cnt(ev.filter((e) => !recente(e)), r39))} | metade recente ${fmtSub(...cnt(ev.filter(recente), r39))}`);
    const c49 = cnt(ev, r49);
    L.push(`   Quando NÃO pagou aos 39, pagou na janela dos 49: ${fmtTaxa(c49[0], c49[1], P6)}  <- o "garantido" do dono`);
    L.push(`      metade antiga ${fmtSub(...cnt(ev.filter((e) => !recente(e)), r49))} | metade recente ${fmtSub(...cnt(ev.filter(recente), r49))}`);
    const c3949 = cnt(ev, (e) => (e.hit49 !== undefined ? e.hit39 || e.hit49 : null));
    L.push(`   Pagou em 39 OU 49: ${fmtTaxa(c3949[0], c3949[1], 1 - (1 - P6) * (1 - P6))}`);
    const rg = (nome, f) => {
      const A = ev.filter((e) => f(e)), B = ev.filter((e) => !f(e));
      L.push(`   ${nome}: aos 39 com ${fmtSub(...cnt(A, r39))} | sem ${fmtSub(...cnt(B, r39))}; aos 49 (se falhou aos 39) com ${fmtSub(...cnt(A, r49))} | sem ${fmtSub(...cnt(B, r49))}`);
    };
    rg('Com repetição na hora da janela', (e) => e.ctx.rep);
    rg('Com pretas altas na hora da janela', (e) => e.ctx.altas);
    rg('Com repetição E pretas altas (regime)', (e) => e.ctx.rep && e.ctx.altas);

    /* D) pedra 5 vermelha 10 minutos antes */
    L.push('');
    L.push('D) PEDRA 5 VERMELHA 10 MINUTOS ANTES DO MINUTO-ALVO (alerta)');
    const al = (nome, flag, alvo) => {
      const base = ev.filter((e) => e.dentroAlerta && (alvo === 39 || (!e.hit39 && e.hit49 !== undefined)));
      const r = (e) => (alvo === 39 ? e.hit39 : e.hit49);
      L.push(`   ${nome}: com a pedra 5 ${fmtSub(...cnt(base.filter((e) => e[flag]), r))} | sem a pedra 5 ${fmtSub(...cnt(base.filter((e) => !e[flag]), r))} (acaso ${pc(P6)})`);
    };
    al('Janela dos 39 (alerta no minuto M+29)', 'a29', 39);
    al('Janela dos 49, quando não pagou aos 39 (alerta no minuto M+39)', 'a39', 49);

    /* E) sinais 12 e 11 dentro da janela dos 39 */
    L.push('');
    L.push('E) SINAIS 12 E 11 DENTRO DA JANELA DOS 39');
    const a12 = [], a12b = [], a11 = [], a11n = [], a1211 = [];
    for (const e of ev) {
      const i12 = e.w39.find((i) => H[i].n === 12);
      if (i12 !== undefined && i12 + 4 < N) {
        const seg4 = [1, 2, 3, 4].map((x) => H[i12 + x]);
        const ok4 = seg4.some((x) => x.n === 0);
        a12.push(ok4);
        if (!ok4 && e.hit49 !== undefined) a12b.push(e.hit49);
        if (seg4.some((x) => x.n === 11)) a1211.push(ok4 ? true : (e.hit49 !== undefined ? e.hit49 : null));
      }
      if (!e.hit39 && e.hit49 !== undefined) {
        if (e.w39.some((i) => H[i].n === 11)) a11.push(e.hit49); else a11n.push(e.hit49);
      }
    }
    const f1 = (arr) => [arr.filter((x) => x !== null).length, arr.filter((x) => x === true).length];
    L.push(`   Saiu 12 na janela dos 39 -> branco nas 4 pedras seguintes: ${fmtTaxa(...f1(a12), p0Branco(4))}`);
    L.push(`   Saiu 12, não pagou em 4 pedras -> pagou na janela dos 49: ${fmtTaxa(...f1(a12b), P6)}`);
    L.push(`   Saiu 11 na janela dos 39 e não pagou -> pagou aos 49: ${fmtTaxa(...f1(a11), P6)} | sem o 11: ${fmtSub(...f1(a11n))}`);
    L.push(`   12 seguido de 11 em 4 pedras -> branco nas 4 pedras ou aos 49: ${fmtTaxa(...f1(a1211), 1 - Math.pow(14 / 15, 10))}`);
    /* F) somas do branco (minuto do branco + valor das pedras vizinhas) */
    L.push('');
    L.push('F) SOMAS DO BRANCO (minuto do branco + pedras vizinhas; 10 a 14 viram 1 dígito: 13 = 1+3 = 4)');
    const red = (n) => (n >= 10 ? Math.floor(n / 10) + (n % 10) : n);
    const NOMES = ['frente 1', 'frente 2', 'frente 1+2', 'trás 1', 'trás 2', 'trás 1+2', 'as 4 juntas'];
    const mkAgg = () => ({ ex: { n: 0, h: 0 }, tol: { n: 0, h: 0 } });
    const AG = { W: NOMES.map(mkAgg), C: NOMES.map(mkAgg) };
    const ANY = { W: mkAgg(), C: mkAgg() };
    const AGcol = NOMES.map(mkAgg); const ANYcol = mkAgg();
    const somaMin = new Set();
    const ANYm = { Wa: mkAgg(), Wb: mkAgg(), Wrep: mkAgg(), Wnrep: mkAgg(), Walt: mkAgg(), Wnalt: mkAgg() };
    const branco = (a, b) => { // 1 se tem branco entre minutos a..b; null se incompleto
      if (b > ultMin - 1) return null;
      let c = 0, w = 0;
      for (let m = a; m <= b; m++) { const l = mm.get(m); if (l) for (const x of l) { c++; if (H[x].n === 0) w = 1; } }
      return c >= 2 * (b - a + 1) - 1 ? w : null;
    };
    for (let i = 2; i < N - 2; i++) {
      if (SEG[i - 2] !== SEG[i + 2]) continue;
      const eh = H[i].n === 0;
      const T = Math.floor(H[i].t / MIN);
      const difMin = (j) => Math.floor(H[j].t / MIN) !== T;
      const colDif = eh && ((H[i - 1].n === 0 && difMin(i - 1)) || (H[i + 1].n === 0 && difMin(i + 1)));
      const v = [red(H[i + 1].n), red(H[i + 2].n), 0, red(H[i - 1].n), red(H[i - 2].n), 0, 0];
      v[2] = v[0] + v[1]; v[5] = v[3] + v[4]; v[6] = v[2] + v[5];
      if (eh) for (let q = 0; q < 7; q++) if (v[q] > 0) somaMin.add(T + v[q]);
      let anyEx = null, anyTol = null; let completo = true;
      const ag = eh ? (colDif ? AGcol : AG.W) : AG.C;
      for (let q = 0; q < 7; q++) {
        const k = v[q]; if (k <= 0) continue;
        const e = branco(T + k, T + k);
        const tt = branco(Math.max(T + 1, T + k - 1), T + k + 1);
        if (e === null || tt === null) { completo = false; continue; }
        ag[q].ex.n++; ag[q].ex.h += e; ag[q].tol.n++; ag[q].tol.h += tt;
        anyEx = anyEx || e; anyTol = anyTol || tt;
      }
      if (completo && anyEx !== null) {
        const o = eh ? (colDif ? ANYcol : ANY.W) : ANY.C;
        o.ex.n++; o.ex.h += anyEx; o.tol.n++; o.tol.h += anyTol;
        if (eh && !colDif) {
          const add = (x) => { x.ex.n++; x.ex.h += anyEx; x.tol.n++; x.tol.h += anyTol; };
          add(i < N / 2 ? ANYm.Wa : ANYm.Wb);
          const c = ctxEm(i);
          add(c.rep ? ANYm.Wrep : ANYm.Wnrep); add(c.altas ? ANYm.Walt : ANYm.Wnalt);
        }
      }
    }
    const z2 = (a, b) => {
      if (!a.n || !b.n) return 0;
      const pc2 = (a.h + b.h) / (a.n + b.n); if (pc2 <= 0 || pc2 >= 1) return 0;
      return (a.h / a.n - b.h / b.n) / Math.sqrt(pc2 * (1 - pc2) * (1 / a.n + 1 / b.n));
    };
    const linhaF = (nome, w, c) => `   ${nome}: brancos ${fmtSub(w.n, w.h)} | controle (pedras comuns) ${fmtSub(c.n, c.h)} | z=${z2(w, c).toFixed(1)}`;
    L.push('   Horário exato (as 2 pedras do minuto da soma):');
    NOMES.forEach((nm, q) => L.push(linhaF(nm, AG.W[q].ex, AG.C[q].ex)));
    L.push(linhaF('QUALQUER das somas', ANY.W.ex, ANY.C.ex));
    L.push('   Com 1 minuto de tolerância (6 pedras):');
    NOMES.forEach((nm, q) => L.push(linhaF(nm, AG.W[q].tol, AG.C[q].tol)));
    L.push(linhaF('QUALQUER das somas', ANY.W.tol, ANY.C.tol));
    L.push(`   "QUALQUER" (horário exato) - metade antiga ${fmtSub(ANYm.Wa.ex.n, ANYm.Wa.ex.h)} | metade recente ${fmtSub(ANYm.Wb.ex.n, ANYm.Wb.ex.h)}`);
    L.push(`   "QUALQUER" (horário exato) - com repetição ${fmtSub(ANYm.Wrep.ex.n, ANYm.Wrep.ex.h)} | sem ${fmtSub(ANYm.Wnrep.ex.n, ANYm.Wnrep.ex.h)} | com pretas altas ${fmtSub(ANYm.Walt.ex.n, ANYm.Walt.ex.h)} | sem ${fmtSub(ANYm.Wnalt.ex.n, ANYm.Wnalt.ex.h)}`);
    L.push('   Brancos colados em MINUTOS DIFERENTES (fora das contas acima, só para observar):');
    NOMES.forEach((nm, q) => { if (AGcol[q].ex.n) L.push(linhaF(nm + ' (exato)', AGcol[q].ex, AG.C[q].ex)); });
    L.push(linhaF('QUALQUER (exato)', ANYcol.ex, ANY.C.ex));
    L.push(linhaF('QUALQUER (com tolerância)', ANYcol.tol, ANY.C.tol));
    L.push('   Controle = o MESMO cálculo feito a partir de pedras que não são branco. Se o branco não tem taxa maior que o controle, a soma não ajuda.');
    L.push('   Com 7 horários e tolerância, "cair um branco em algum" acontece quase sempre por sorte: só vale a diferença para o controle.');
    /* G) sequência de N em N minutos a partir de um branco */
    L.push('');
    L.push('G) SEQUÊNCIA DE 3 EM 3 MINUTOS: branco em minuto terminado em 3 ou 9 -> deveria vir branco a cada 3 minutos seguintes (T+3, T+6, T+9...)');
    const digMin = (m) => new Date(m * MIN).getMinutes() % 10;
    const b39Min = new Set();
    for (const M of duplas) { for (let d = 38; d <= 40; d++) b39Min.add(M + d); for (let d = 48; d <= 50; d++) b39Min.add(M + d); }
    const engMin0 = ENG_T0 ? Math.floor(ENG_T0 / MIN) + 60 : Infinity;
    const cadeia = (passo, digs, K, deep) => {
      const novo = () => ({ n: 0, k: Array(K).fill(0), tot: 0, ge: [0, 0, 0, 0, 0], n3: 0, a3: 0, run: 0, recs: [] });
      const W = novo(), Cc = novo();
      for (const [m, l] of mm) {
        if (digs && !digs.includes(digMin(m))) continue;
        if (l.length < 2 || m + passo * K > ultMin - 1) continue;
        const eh = l.some((x) => H[x].n === 0);
        const hits = []; const rc = []; let ok = true;
        for (let k = 1; k <= K; k++) {
          const Mt = m + passo * k;
          const r = branco(Mt, Mt);
          if (r === null) { ok = false; break; }
          hits.push(r);
          if (deep) { const ls = mm.get(Mt); rc.push({ hit: r, Mt, idx: ls ? ls[0] - 1 : -1 }); }
        }
        if (!ok) continue;
        const A = eh ? W : Cc;
        A.n++; hits.forEach((h, k) => { A.k[k] += h; });
        const tot = hits.reduce((a, b) => a + b, 0); A.tot += tot;
        for (let g = 1; g <= 4; g++) if (tot >= g) A.ge[g]++;
        const any3 = hits.slice(0, 3).some((x) => x) ? 1 : 0;
        A.n3++; A.a3 += any3;
        let run = 0; while (run < K && hits[run]) run++; A.run += run;
        if (deep) { for (const r of rc) A.recs.push(r); if (eh) A.ini = (A.ini || []).concat([{ m, any3, idx: l[0] }]); }
      }
      return { W, C: Cc };
    };
    const mostrar = (nome, passo, digs, K, deep) => {
      const { W, C: Cc } = cadeia(passo, digs, K, deep);
      L.push(`   ${nome}: ${W.n} inícios com branco | ${Cc.n} minutos de controle (sem branco)`);
      if (!W.n || !Cc.n) return;
      const ps = [];
      for (let k = 0; k < K; k++) ps.push(`+${passo * (k + 1)}: ${pc(W.k[k] / W.n)} (ctrl ${pc(Cc.k[k] / Cc.n)}, z=${z2({ n: W.n, h: W.k[k] }, { n: Cc.n, h: Cc.k[k] }).toFixed(1)})`);
      L.push('     por passo (minutos depois do branco): ' + ps.join(' | '));
      L.push(`     quantos dos ${K} passos pagaram (média): ${(W.tot / W.n).toFixed(2).replace('.', ',')} | controle ${(Cc.tot / Cc.n).toFixed(2).replace('.', ',')}`);
      L.push('     ' + [1, 2, 3, 4].map((g) => `${g}+ passos: ${pc(W.ge[g] / W.n)} (ctrl ${pc(Cc.ge[g] / Cc.n)}, z=${z2({ n: W.n, h: W.ge[g] }, { n: Cc.n, h: Cc.ge[g] }).toFixed(1)})`).join(' | '));
      L.push(`     pelo menos 1 dos 3 primeiros passos: ${fmtSub(W.n3, W.a3)} | controle ${fmtSub(Cc.n3, Cc.a3)} | z=${z2({ n: W.n3, h: W.a3 }, { n: Cc.n3, h: Cc.a3 }).toFixed(1)}`);
      L.push(`     passos seguidos que pagaram desde o início (média): ${(W.run / W.n).toFixed(2).replace('.', ',')} | controle ${(Cc.run / Cc.n).toFixed(2).replace('.', ',')}`);
      if (!deep) return;
      if (W.ini && W.ini.length) {
        const meio = W.ini[Math.floor(W.ini.length / 2)].m;
        const sub = (f) => { const a = W.ini.filter(f); return fmtSub(a.length, a.reduce((x, e) => x + e.any3, 0)); };
        L.push(`     "1+ dos 3 primeiros": metade antiga ${sub((e) => e.m < meio)} | metade recente ${sub((e) => e.m >= meio)}`);
      }
      // condições do gráfico e das outras estratégias no horário de cada passo
      const prep = (R) => R.forEach((r) => {
        r.c = r.idx >= 1 ? ctxEm(r.idx) : { rep: false, altas: false };
        const es = new Set(); let tem = false;
        if (r.Mt >= engMin0) { tem = true; for (let d = -1; d <= 1; d++) { const s = EST_MIN.get(r.Mt + d); if (s) s.forEach((x) => es.add(x)); } }
        r.es = tem ? es : null; r.soma = somaMin.has(r.Mt); r.j39 = b39Min.has(r.Mt);
      });
      prep(W.recs); prep(Cc.recs);
      const split = (nome, f, so) => {
        const part = (R) => { const a = { n: 0, h: 0 }, b = { n: 0, h: 0 }; for (const r of R) { if (so && !so(r)) continue; const t = f(r) ? a : b; t.n++; t.h += r.hit; } return [a, b]; };
        const [wa, wb] = part(W.recs), [ca, cb] = part(Cc.recs);
        L.push(`     ${nome}: com ${fmtSub(wa.n, wa.h)} (ctrl ${fmtSub(ca.n, ca.h)}, z=${z2(wa, ca).toFixed(1)}) | sem ${fmtSub(wb.n, wb.h)} (ctrl ${fmtSub(cb.n, cb.h)})`);
      };
      L.push('     Taxa de pagar em cada passo, conforme as condições NAQUELE horário:');
      split('repetição no gráfico', (r) => r.c.rep);
      split('pretas altas no gráfico', (r) => r.c.altas);
      split('regime (repetição + pretas altas)', (r) => r.c.rep && r.c.altas);
      split('soma do branco (item F) caindo nesse horário', (r) => r.soma);
      split('janela dos 39/49 de uma dupla nesse horário', (r) => r.j39);
      for (const e of ['B39', 'PA', 'BC', 'W']) split(`estratégia ${NOME_EST[e] || 'Wall'} com entrada nesse horário (±1 min)`, (r) => r.es.has(e), (r) => r.es !== null);
    };
    mostrar('Passo 3, início só em minuto terminado em 3 ou 9 (regra do dono), seguindo 12 passos (36 min)', 3, [3, 9], 12, true);
    mostrar('Passo 3, início em qualquer minuto (para ver se 3 e 9 são mesmo especiais)', 3, null, 6, false);
    mostrar('Passo 4, início em qualquer minuto', 4, null, 6, false);
    mostrar('Passo 5, início em qualquer minuto', 5, null, 6, false);
    mostrar('Passo 7, início em qualquer minuto', 7, null, 6, false);
    L.push('   Controle = minutos com a mesma terminação, mas SEM branco. Só vale se o branco ficar bem acima do controle.');
    L.push('   As estratégias (B39, PA, BC, Wall) só existem para o período em que o motor rodou (últimas ~3000 pedras + ao vivo).');
    L.push('');
    L.push('   Leitura: "acaso" é o que se esperaria num sorteio puro. Só vale se bater nas duas metades e com z alto');
    L.push('   (z maior que ~3,4 = difícil de ser sorte, já descontando que muitas regras estão sendo testadas).');
    return L;
  }

  /* ---------- observatório ao vivo: avisa na conversa quando uma regra do dono entra em ação ---------- */
  const ativas = [];
  const somas = [];
  let seq3 = null;
  const fimSeq = (q, t) => {
    const ks = Object.keys(q.hit).map(Number).sort((x, y) => x - y);
    emitir('resumo', `🔁 Sequência de 3 em 3 do minuto ${hmin(q.T)} terminou: pagou em ${ks.length} dos 12 passos${ks.length ? ` (passos ${ks.join(', ')})` : ''}.`, t);
  };
  function vivoObs(i) {
    const { n, t } = H[i];
    const m = Math.floor(t / MIN);
    if (n === 0 && i > 0 && H[i - 1].n === 0 && Math.floor(H[i - 1].t / MIN) === m && SEG[i - 1] === SEG[i] && !ativas.some((a) => a.M === m)) {
      ativas.push({ M: m, w39: null, w49: null, al29: false, al39: false, s12: null, s11: false });
      emitir('branco', `⚪⚪ Dupla no minuto ${hmin(m)} (os dois brancos no mesmo minuto). Janela dos 39: ${hmin(m + 38)} a ${hmin(m + 40)}. Janela dos 49: ${hmin(m + 48)} a ${hmin(m + 50)}. Alerta (pedra 5 vermelha) esperado às ${hmin(m + 29)}.`, t);
    }
    if (i >= 4 && H[i - 2].n === 0 && SEG[i - 4] === SEG[i] && !somas.some((x) => x.i === i - 2)) {
      const red = (x) => (x >= 10 ? Math.floor(x / 10) + (x % 10) : x);
      const j = i - 2, a = red(H[j + 1].n), b = red(H[j + 2].n), c = red(H[j - 1].n), d = red(H[j - 2].n);
      const Tm = Math.floor(H[j].t / MIN);
      const alvos = [['frente 1', a], ['frente 2', b], ['frente 1+2', a + b], ['trás 1', c], ['trás 2', d], ['trás 1+2', c + d], ['4 juntas', a + b + c + d]].filter((x) => x[1] > 0);
      somas.push({ i: j, Tm, alvos });
      const lista = alvos.map(([nm, k]) => `${hmin(Tm + k)} (${nm})`).join(', ');
      const colDifV = (H[j - 1].n === 0 && Math.floor(H[j - 1].t / MIN) !== Tm) || (H[j + 1].n === 0 && Math.floor(H[j + 1].t / MIN) !== Tm);
      emitir('estrat', `🧮 Somas do branco das ${hms(H[j].t)}${colDifV ? ' (colado em outro minuto: só observação)' : ''} [trás ${d} ${c} | frente ${a} ${b}]: ${lista}.`, t);
    }
    if (n === 0) {
      for (const x of somas) {
        for (const [nm, k] of x.alvos) {
          if (x.Tm + k === m) emitir('ok', `✅ Branco às ${hms(t)} bateu com a soma "${nm}" do branco das ${hmin(x.Tm)}.`, t);
        }
      }
    }
    while (somas.length && m - somas[0].Tm > 60) somas.shift();
    const condAgora = (mm0) => {
      const c = ctxEm(i);
      const co = [];
      for (let d = -1; d <= 1; d++) { const sx = EST_MIN.get(mm0 + d); if (sx) sx.forEach((x) => { const nm = NOME_EST[x] || (x === 'W' ? 'Wall' : null); if (nm && !co.includes(nm)) co.push(nm); }); }
      if (somas.some((x) => x.alvos.some(([, k]) => x.Tm + k === mm0))) co.push('soma do branco');
      if (ativas.some((x) => { const d2 = mm0 - x.M; return (d2 >= 38 && d2 <= 40) || (d2 >= 48 && d2 <= 50); })) co.push('janela 39/49');
      return `repetição: ${c.rep ? 'sim' : 'não'} · pretas altas: ${c.altas ? 'sim' : 'não'} · coincide com: ${co.length ? co.join(', ') : 'nenhuma estratégia'}`;
    };
    if (n === 0) {
      const dg = new Date(m * MIN).getMinutes() % 10;
      const dk = seq3 ? m - seq3.T : -1;
      if (seq3 && dk > 0 && dk % 3 === 0 && dk / 3 <= 12) {
        const k = dk / 3;
        if (!seq3.hit[k]) { seq3.hit[k] = true; emitir('ok', `✅ Sequência de 3 em 3 (início ${hmin(seq3.T)}): branco no passo ${k} (+${dk}min) às ${hms(t)} · ${condAgora(m)}.`, t); }
      } else if ((dg === 3 || dg === 9) && !(seq3 && m === seq3.T)) {
        if (seq3) fimSeq(seq3, t);
        seq3 = { T: m, hit: {} };
        const al = [1, 2, 3, 4, 5, 6].map((k) => hmin(m + 3 * k)).join(', ');
        emitir('estrat', `🔁 Branco no minuto ${hmin(m)} (final ${dg}): sequência de 3 em 3 minutos começa. Próximos horários: ${al}... (acompanho até 12 passos).`, t);
      }
    }
    if (seq3 && m > seq3.T + 3 * 12 + 1) { fimSeq(seq3, t); seq3 = null; }
    for (let q = ativas.length - 1; q >= 0; q--) {
      const a = ativas[q]; const d = m - a.M;
      if (d > 60) { ativas.splice(q, 1); continue; }
      if (d === 29 && n === 5 && !a.al29) { a.al29 = true; emitir('chute', `🔔 Pedra 5 vermelha às ${hms(t)}: alerta de que o branco dos 39 (dupla de ${hmin(a.M)}) deve vir por volta de ${hmin(a.M + 39)}.`, t); }
      if (d === 39 && n === 5 && !a.al39 && a.w39 !== 'hit') { a.al39 = true; emitir('chute', `🔔 Pedra 5 vermelha às ${hms(t)}: alerta para o branco dos 49 (dupla de ${hmin(a.M)}), por volta de ${hmin(a.M + 49)}.`, t); }
      if (d >= 38 && d <= 40) {
        if (n === 0 && a.w39 === null) { a.w39 = 'hit'; emitir('ok', `✅ Branco na janela dos 39 (dupla de ${hmin(a.M)}) às ${hms(t)}.`, t); }
        if (n === 12 && a.w39 === null && !a.s12) { a.s12 = { i }; emitir('regime', `12 às ${hms(t)} na janela dos 39: segundo o dono, branco deve vir nas próximas 4 pedras.`, t); }
        if (n === 11 && a.w39 === null && !a.s11) { a.s11 = true; emitir('info', `11 às ${hms(t)} na janela dos 39 (dupla de ${hmin(a.M)}).`, t); }
      }
      if (a.s12 && !a.s12.fim) {
        const dist12 = i - a.s12.i;
        if (dist12 > 0 && dist12 <= 4 && n === 0) { a.s12.fim = true; emitir('ok', `✅ Branco veio ${dist12} pedra(s) depois do 12.`, t); }
        else if (dist12 === 4) { a.s12.fim = true; emitir('erro', '❌ O 12 não pagou nas 4 pedras seguintes. Pela regra, espera-se na janela dos 49.', t); }
      }
      if (d > 40 && a.w39 === null) { a.w39 = 'miss'; emitir('erro', `❌ Janela dos 39 NÃO pagou (dupla de ${hmin(a.M)}). Pela regra, vem na janela dos 49: ${hmin(a.M + 48)} a ${hmin(a.M + 50)}.`, t); }
      if (d >= 48 && d <= 50 && a.w39 === 'miss' && a.w49 === null && n === 0) { a.w49 = 'hit'; emitir('ok', `✅ Branco na janela dos 49 (dupla de ${hmin(a.M)}) às ${hms(t)}.`, t); }
      if (d > 50 && a.w39 === 'miss' && a.w49 === null) { a.w49 = 'miss'; emitir('erro', `❌ Janela dos 49 também NÃO pagou (dupla de ${hmin(a.M)}).`, t); }
    }
  }

  /* ---------- falas do cérebro sobre o que está vendo (só ao vivo) ---------- */
  function falar(f) {
    const t = f.t;
    const muda = (chave, novo, txtOn, txtOff) => {
      if (novo === flags[chave]) return;
      if (t - (flags.ult[chave] || 0) < 180000) return;
      flags.ult[chave] = t; flags[chave] = novo;
      emitir(novo ? 'regime' : 'info', novo ? txtOn : txtOff, t);
    };
    const dr = defRep(), da = defAltas();
    const dRep = distEm(f.i, dr.W);
    const pAlt = da.ap ? propEm(f.i, da.m, da.W) : f.prop;
    const novoRep = flags.rep ? !(dRep !== null && dRep >= dr.d + 2) : (dRep !== null && dRep <= dr.d);
    const novoAltas = flags.altas ? !(pAlt !== null && pAlt < da.sai) : (pAlt !== null && pAlt >= da.ent);
    const qual = (a) => (a ? '' : ' [definição padrão: ainda sem prova]');
    muda('rep', novoRep, `🔁 Repetição LIGADA: só ${dRep} valores diferentes nas últimas ${dr.W} pedras${qual(dr.ap)}.`, '🔁 Repetição desligada (voltou ao normal).');
    muda('altas', novoAltas, `⬛ Pretas altas em alta: ${Math.round((pAlt || 0) * 100)}% das pretas recentes são ${da.m}-14 (por acaso ${pc((15 - da.m) / 7)})${qual(da.ap)}.`, '⬛ Pretas altas voltaram ao normal.');
    muda('reg', novoRep && novoAltas, '🔶 REGIME: repetição e pretas altas ao mesmo tempo.', '🔶 Regime terminou.');
    if (f.n === 0) {
      if (f.secaMin === 0 && secaMarcas.has(30)) emitir('branco', `⚪ Branco às ${hms(t)} encerra a seca. Vamos ver se vem o segundo colado.`, t);
      secaMarcas = new Set();
    } else if (f.secaMin !== null) {
      for (const m of [20, 30, 40, 49, 60, 90, 120]) {
        if (f.secaMin >= m && !secaMarcas.has(m)) { secaMarcas.add(m); emitir('seca', `⏳ ${m} minutos sem branco (${f.secaPed} pedras).`, t); }
      }
    }
    if (f.duplaFim) emitir('branco', `⚪⚪ Dois brancos colados (${hms(t)}) encerrando uma seca de 30+ min.`, t);
    else if (f.colados) emitir('branco', `⚪⚪ Dois brancos colados (${hms(t)}).`, t);
    if (f.soloFim) emitir('branco', '⚪ O branco que encerrou a seca ficou sozinho (sem segundo colado).', t);
  }

  /* ---------- estratégias: como cada uma se sai em cada circunstância ---------- */
  const ctxDe = (f) => ({ rep: !!(f && f.rep), altas: !!(f && f.altasReg), reg: !!(f && f.reg3), seca: !!(f && f.secaMin !== null && f.secaMin >= 20) });
  function somar(grupo, est, e) {
    const g = (ST[grupo][est] = ST[grupo][est] || {});
    const c = e.ctx || {};
    const add = (k) => { const x = (g[k] = g[k] || { g: 0, l: 0 }); if (e.estado === 'green') x.g++; else x.l++; };
    add('tot');
    add(c.rep ? 'rep1' : 'rep0');
    add(c.altas ? 'alt1' : 'alt0');
    add(c.reg ? 'reg1' : 'reg0');
    add(c.seca ? 'seca1' : 'seca0');
  }
  function rodarEstrategias(i, now, fase) {
    addStone(eng, { id: i + 1, n: H[i].n, t: H[i].t });
    const novas = avancar(eng, now, null, {}, []);
    for (const e of eng.entradas) if (e.ctx === undefined) e.ctx = ctxDe(fAtual);
    for (; engReg < eng.entradas.length; engReg++) { const e = eng.entradas[engReg]; let st = EST_MIN.get(e.M); if (!st) { st = new Set(); EST_MIN.set(e.M, st); } st.add(e.est); }
    if (!ENG_T0) ENG_T0 = H[i].t;
    for (const e of novas) {
      if (!NOME_EST[e.est] || (e.estado !== 'green' && e.estado !== 'loss')) continue;
      somar(fase === 'vivo' ? 'vivo' : 'hist', e.est, e);
      if (fase === 'vivo') {
        const c = e.ctx || {};
        emitir('estrat', `${e.estado === 'green' ? '✅' : '❌'} ${NOME_EST[e.est]} ${hhmm(e.M)} ${e.estado === 'green' ? 'acertou' : 'não acertou'} · repetição: ${c.rep ? 'sim' : 'não'} · pretas altas: ${c.altas ? 'sim' : 'não'} · seca 20+ min: ${c.seca ? 'sim' : 'não'}`, now);
        sujo = true;
      }
    }
  }

  /* ---------- ligar: lê o histórico guardado e treina ---------- */
  function adicionarPedra(n, t) {
    const i = H.length;
    H.push({ n, t });
    SEG.push(i === 0 || t - H[i - 1].t > GAP_MS ? i : SEG[i - 1]);
    return i;
  }

  async function iniciar(pedras, aoProgresso) {
    carregarEstado();
    silencio = true;
    const lista = pedras.slice(-MAX_PEDRAS);
    carregadas = lista.length;
    const N = lista.length;
    const split = N >= 600 ? Math.floor(N * 0.7) : N;
    const ini = Math.max(0, N - REPLAY_ENGINE);
    const t0 = Date.now();
    sempre('info', `🧠 Cérebro ligado. Lendo ${N} pedras guardadas${N ? ` (de ${dmhms(lista[0].t)} até ${dmhms(lista[N - 1].t)})` : ''}...`);
    for (let a = 0; a < N; a += 3000) {
      const b = Math.min(N, a + 3000);
      for (let k = a; k < b; k++) {
        const i = adicionarPedra(lista[k].n, lista[k].t);
        passo(i, k < split ? 'treino' : 'teste');
        if (k >= N - 600) vivoObs(i);
        if (k >= ini) rodarEstrategias(i, lista[k].t + 25000, 'hist');
      }
      if (aoProgresso) aoProgresso(b / N);
      await new Promise((r) => setTimeout(r, 0));
    }
    silencio = false;
    let trechos = 0;
    for (let i = 0; i < H.length; i++) if (SEG[i] === i) trechos++;
    const cont = { 'confirmada': 0, 'promissora': 0, 'observar': 0 };
    HIP.forEach((h) => { const s = status(h); if (cont[s] !== undefined) cont[s]++; });
    sempre('info', `📚 Li ${N} pedras em ${trechos} trecho(s) contínuo(s), testei ${HIP.length} hipóteses (${((Date.now() - t0) / 1000).toFixed(1)} s).`);
    const top = HIP.filter((h) => status(h) !== 'sem evidência').map((h) => ({ h, z: Math.abs(zsc(h.fases.treino.n, h.fases.treino.h, h.p0)) })).sort((a, b) => b.z - a.z).slice(0, 5);
    if (!top.length) sempre('descoberta', `🔎 Nenhuma hipótese se destacou do acaso ainda${N < 3000 ? ` (poucos dados: ${N} pedras; o ideal é 20 mil ou mais)` : ''}. Seguimos observando.`);
    else {
      sempre('descoberta', `🔎 Hipóteses que mais se destacaram (treino contra teste):`);
      for (const { h } of top) {
        const tr = h.fases.treino, te = h.fases.teste;
        sempre('descoberta', `• ${h.nome} [${status(h)}] treino ${pc(taxa(tr))} (${tr.n} casos), teste ${te.n ? pc(taxa(te)) : '—'} (${te.n} casos), acaso ${pc(h.p0)}.`);
      }
    }
    try { aprenderRegimes(); } catch (e) { sempre('info', 'Aprendiz de regime falhou: ' + e.message); }
    pronto = true;
    ultResumo = Date.now();
    const f = fila; fila = [];
    f.forEach((s) => pedra(s));
    sujo = true;
    salvar(true);
  }

  /* ---------- pedra ao vivo ---------- */
  function pedra(st) {
    if (!pronto) { fila.push(st); return; }
    if (H.length && st.t <= H[H.length - 1].t) return;
    const i = adicionarPedra(st.n, st.t);
    const f = passo(i, 'vivo');
    vivoObs(i);
    falar(f);
    rodarEstrategias(i, Date.now(), 'vivo');
    if (Date.now() - ultResumo > 30 * MIN) resumo();
    sujo = true;
  }

  function resumo() {
    ultResumo = Date.now();
    try { aprenderRegimes(); } catch (e) {}
    const partes = [];
    partes.push(`chutes: ${placar.h} de ${placar.n} (acaso ~${placar.esp.toFixed(1).replace('.', ',')})`);
    for (const e of ['B39', 'PA', 'BC']) {
      const g = ST.vivo[e] && ST.vivo[e].tot;
      if (g && g.g + g.l) partes.push(`${NOME_EST[e]} ${g.g}✅ ${g.l}❌`);
    }
    emitir('resumo', `📋 Resumo: ${partes.join(' · ')}.`);
  }

  /* ---------- relatório em texto ---------- */
  function linhaHip(h) {
    const tr = h.fases.treino, te = h.fases.teste, vv = h.fases.vivo;
    const t = (c) => (c.n ? `${pc(taxa(c))}/${c.n}` : '—');
    return `- ${h.nome}\n    [${status(h)}] acaso ${pc(h.p0)} | treino ${t(tr)} | teste ${t(te)} | ao vivo ${t(vv)}`;
  }
  function blocoEst(grupo) {
    const out = [];
    for (const e of ['B39', 'PA', 'BC']) {
      const g = ST[grupo][e];
      if (!g || !g.tot) { out.push(`  ${NOME_EST[e]}: sem entradas ainda`); continue; }
      const p = (k) => (g[k] && g[k].g + g[k].l ? `${pc(g[k].g / (g[k].g + g[k].l))} (${g[k].g}/${g[k].g + g[k].l})` : '—');
      out.push(`  ${NOME_EST[e]}: total ${p('tot')}`);
      out.push(`     com repetição ${p('rep1')} | sem ${p('rep0')}`);
      out.push(`     com pretas altas ${p('alt1')} | sem ${p('alt0')}`);
      out.push(`     em regime ${p('reg1')} | fora ${p('reg0')}`);
      out.push(`     com seca 20+ min ${p('seca1')} | sem ${p('seca0')}`);
    }
    return out.join('\n');
  }
  function relatorio() {
    const f = fAtual;
    const cont = { 'confirmada': 0, 'promissora': 0, 'observar': 0, 'sem evidência': 0 };
    HIP.forEach((h) => { cont[status(h)]++; });
    const ordem = [...HIP].sort((a, b) => Math.abs(zsc(b.fases.treino.n, b.fases.treino.h, b.p0)) - Math.abs(zsc(a.fases.treino.n, a.fases.treino.h, a.p0)));
    const dono = ['u12r1_b4', 'u12r3_b4', 'u13r3_b4', 'u10r3_b2', 'fimSolo_b20', 'fimDupla_b20', 'col_rep10', 'solo_rep10']
      .map((id) => HIDX[id]).filter(Boolean);
    const L = [];
    L.push(`RELATÓRIO DO CÉREBRO - ${dmhms(Date.now())}`);
    L.push('');
    L.push(`Pedras analisadas: ${H.length}${H.length ? ` (de ${dmhms(H[0].t)} até ${dmhms(H[H.length - 1].t)})` : ''}`);
    L.push(`Hipóteses: ${HIP.length} | confirmadas ${cont['confirmada']} | promissoras ${cont['promissora']} | a observar ${cont['observar']} | sem evidência ${cont['sem evidência']}`);
    L.push(`Chutes ao vivo: ${placar.h} acertos em ${placar.n} (por acaso seriam ~${placar.esp.toFixed(1).replace('.', ',')})`);
    L.push('');
    L.push('GRÁFICO AGORA');
    if (f) {
      L.push(`- Valores diferentes nas últimas 10 pedras: ${f.dist === null ? '—' : f.dist} (acaso ~7,5)`);
      L.push(`- Pretas altas (${ALTA_MIN}-14) nas últimas pretas: ${f.prop === null ? '—' : `${f.altas} de ${f.pretas} (${pc(f.prop)})`} (acaso ${pc((15 - ALTA_MIN) / 7)})`);
      L.push(`- Sem branco há: ${f.secaMin === null ? '—' : `${Math.floor(f.secaMin)} min (${f.secaPed} pedras)`}`);
      L.push(`- Regime: repetição ${f.rep ? 'SIM' : 'não'} | pretas altas ${f.altasReg ? 'SIM' : 'não'}`);
    } else L.push('- ainda sem pedras');
    L.push('');
    L.push('OBSERVATÓRIO DO DONO (regras da Blaze)');
    try { observatorio().forEach((x) => L.push(x)); } catch (e) { L.push('erro no observatório: ' + e.message); }
    L.push('');
    L.push('REGIMES APRENDIDOS (o cérebro testou várias definições)');
    const linhaC = (c, nome) => `  ${nome} -> treino: continua ${pc(c.tr.pCont)} (acaso ${pc(c.tr.pB)}, ${c.tr.nA} casos, z=${c.tr.z.toFixed(1)}) | teste: ${pc(c.te.pCont)} (acaso ${pc(c.te.pB)}, ${c.te.nA} casos, z=${c.te.z.toFixed(1)})`;
    if (!APR.rep) L.push('- ainda sem dados suficientes (precisa de 600+ pedras)');
    else {
      L.push(`Repetição: veredito "${APR.rep.cls}" (melhor: ${APR.rep.d} ou menos valores em ${APR.rep.W} pedras)`);
      APR.tab.rep.slice().sort((a, b) => b.tr.z - a.tr.z).slice(0, 6).forEach((c) => L.push(linhaC(c, `${c.d} ou menos em ${c.W}`)));
      L.push(`Pretas altas: veredito "${APR.altas.cls}" (melhor: ${Math.round(APR.altas.th * 100)}%+ de ${APR.altas.m}-14)`);
      APR.tab.altas.slice().sort((a, b) => b.tr.z - a.tr.z).slice(0, 6).forEach((c) => L.push(linhaC(c, `${Math.round(c.th * 100)}%+ de ${c.m}-14`)));
      L.push('Leitura: "continua" = estando no estado agora, chance de ainda estar nele na janela seguinte. Maior que o acaso nas DUAS fases (treino e teste) = fases reais. Perto do acaso = sorteio.');
    }
    L.push('');
    L.push('HIPÓTESES DO DONO (as que ele descreveu)');
    dono.forEach((h) => L.push(linhaHip(h)));
    L.push('');
    L.push('TOP 15 HIPÓTESES (maior diferença do acaso no treino)');
    ordem.slice(0, 15).forEach((h) => L.push(linhaHip(h)));
    L.push('');
    L.push('ESTRATÉGIAS - AO VIVO');
    L.push(blocoEst('vivo'));
    L.push('');
    L.push('ESTRATÉGIAS - ÚLTIMAS PEDRAS LIDAS AO LIGAR');
    L.push(blocoEst('hist'));
    L.push('');
    L.push('COMO LER');
    L.push('- "acaso" é a taxa esperada se tudo fosse sorteio puro. Valores perto dele = sem efeito.');
    L.push('- treino/teste = passado dividido em duas partes (70%/30%). Só vale se aparecer nas DUAS.');
    L.push('- "ao vivo" = casos novos, depois que o cérebro passou a observar. É a prova mais forte.');
    L.push(`- Foram testadas ${HIP.length} hipóteses ao mesmo tempo; algumas vão parecer boas só por sorte. Por isso a exigência é alta.`);
    L.push('- Isso descreve o passado e mede chutes; não é garantia de acerto futuro.');
    return L.join('\n');
  }
  function conversaTexto() {
    return LINHAS.map((l) => `[${dmhms(l.t)}] ${l.txt}`).join('\n');
  }

  return {
    iniciar, pedra, salvar, relatorio, conversaTexto,
    linhas: () => LINHAS,
    aoLinha: (fn) => { ouvintes.add(fn); return () => ouvintes.delete(fn); },
    total: () => H.length,
    carregadas: () => carregadas,
  };
}
