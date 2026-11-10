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
