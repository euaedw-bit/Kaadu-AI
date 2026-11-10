// Motor das estratégias do Blaze. Só lógica, sem tela.
// Pedra: { id, n (0 = branco, 1..14), t (ms) }.  Entrada: ver criar().
export const MIN = 60000;
export const mi = (t) => Math.floor(t / MIN);
const pad = (n) => String(n).padStart(2, '0');
export const hhmm = (M) => {
  const d = new Date(M * MIN);
  return `${pad(d.getHours())}:${pad(d.getMinutes())}`;
};
export const digitoDe = (M) => new Date(M * MIN).getMinutes() % 10;

export function novoEstado() {
  return {
    stones: [],
    seq: 0,
    entradas: [],
    b39: { usados: {} },
    pa: { fase: 'silencioso', proj: null, lastBaseId: null, ativo: null, d: 0 },
    bc: { fase: 'silencioso', proj: null, lastBaseId: null, hitId: null, lote: null },
    wall: { vistos: {} },
    sa: { ultimoId: null },
    consulta: null,
  };
}

export function addStone(S, stone) {
  S.stones.push(stone);
  if (S.stones.length > 800) S.stones.shift();
}

/* ---------- auxiliares ---------- */
const brancos = (S) => S.stones.filter((s) => s.n === 0);

// tolerância: um branco no minuto da entrada, 1 minuto antes ou 1 minuto depois conta como acerto
export const TOLERANCIA = 1;
// as pedras chegam ~25 s depois da hora marcada (hora = início da rodada), então a janela só
// é dada como terminada depois dessa folga
const FOLGA_CHEGADA = 45000;
const completa = (stones, M, now) =>
  now >= (M + TOLERANCIA + 1) * MIN + FOLGA_CHEGADA || stones.some((s) => mi(s.t) >= M + TOLERANCIA + 1);
const acerto = (stones, M) => stones.find((s) => s.n === 0 && Math.abs(mi(s.t) - M) <= TOLERANCIA) || null;

function criar(S, est, M, now) {
  const e = { id: ++S.seq, est, M, estado: 'pendente', criada: now, hitId: null,
    resolvida: null, forte: false, fogo: false, fontes: [est], alertado: false };
  S.entradas.push(e);
  return e;
}

/* ---------- resolução das entradas (verde / vermelho) ---------- */
function resolverTodas(S, now, novas) {
  const ord = [...S.entradas].sort((a, b) => a.M - b.M);
  for (const e of ord) {
    if (e.estado !== 'pendente' || !completa(S.stones, e.M, now)) continue;
    const h = acerto(S.stones, e.M);
    e.estado = h ? 'green' : 'loss';
    e.hitId = h ? h.id : null;
    e.resolvida = now;
    novas.push(e);
    // Base 39: se a primeira acertou, a de +49 deixa de valer
    if (e.est === 'B39' && e.irmao && e.estado === 'green' && !e.ehPlanoB) {
      const o = S.entradas.find((x) => x.id === e.irmao);
      if (o && o.estado === 'pendente') o.estado = 'anulada';
    }
  }
}

/* ---------- Base 39: dois brancos no mesmo minuto ---------- */
function stepB39(S, now) {
  const porMin = {};
  for (const s of brancos(S)) (porMin[mi(s.t)] = porMin[mi(s.t)] || []).push(s);
  for (const m in porMin) {
    if (porMin[m].length >= 2 && !S.b39.usados[m]) {
      S.b39.usados[m] = true;
      const M1 = +m + 39, M2 = +m + 49;
      if (M2 >= mi(now)) {
        const e1 = criar(S, 'B39', M1, now);
        const e2 = criar(S, 'B39', M2, now);
        e2.ehPlanoB = true;
        e1.irmao = e2.id; e2.irmao = e1.id;
      }
    }
  }
}

/* ---------- PA: sempre checando; só libera depois de acertar ---------- */
// condições para o PA ligar: os 2 últimos brancos com pelo menos 3 minutos de diferença
// (2 minutos de vácuo entre eles) e média dos 3 últimos intervalos também de pelo menos 3
export const PA_GAP_MIN = 3;
export const PA_MEDIA_MIN = 3;
function paPodeAtivar(W) {
  if (W.length < 3) return false;
  const n = W.length;
  const g1 = mi(W[n - 1].t) - mi(W[n - 2].t);
  const g0 = mi(W[n - 2].t) - mi(W[n - 3].t);
  return g1 >= PA_GAP_MIN && (g0 + g1) / 2 >= PA_MEDIA_MIN;
}
const dPar = (W, k) => (k < 1 ? 0 : mi(W[k].t) - mi(W[k - 1].t));

function stepPA(S, now) {
  const pa = S.pa;
  const W = brancos(S);
  for (let g = 0; g < 10; g++) {
    let mudou = false;
    if (pa.fase === 'silencioso') {
      if (pa.proj) {
        const p = pa.proj;
        if (completa(S.stones, p.M, now)) {
          const h = acerto(S.stones, p.M);
          if (h) {
            const k = W.findIndex((w) => w.id === h.id);
            let d = dPar(W, k);
            if (d <= 0) d = p.d;
            pa.d = d;
            const e1 = criar(S, 'PA', mi(h.t) + d, now);
            const e2 = criar(S, 'PA', mi(h.t) + 2 * d, now);
            pa.ativo = [e1.id, e2.id];
            pa.fase = 'ativo';
          } else {
            pa.lastBaseId = p.baseId;
          }
          pa.proj = null;
          mudou = true;
        }
      } else if (W.length >= 3) {
        const b = W[W.length - 1];
        if (b.id !== pa.lastBaseId) {
          const a = W[W.length - 2];
          const d = mi(b.t) - mi(a.t);
          // o cálculo continua só nos 2 últimos brancos; os 3 últimos só liberam a ativação
          if (paPodeAtivar(W)) { pa.proj = { M: mi(b.t) + d, baseId: b.id, d }; mudou = true; }
          else pa.lastBaseId = b.id;
        }
      }
    } else {
      // ativo: só a segunda entrada serve de referência
      const e2 = S.entradas.find((e) => e.id === pa.ativo[1]);
      if (e2 && e2.estado === 'green') {
        const k = W.findIndex((w) => w.id === e2.hitId);
        let d = dPar(W, k);
        if (d <= 0) d = pa.d;
        pa.d = d;
        const h = W[k];
        const n1 = criar(S, 'PA', mi(h.t) + d, now);
        const n2 = criar(S, 'PA', mi(h.t) + 2 * d, now);
        pa.ativo = [n1.id, n2.id];
        mudou = true;
      } else if (e2 && (e2.estado === 'loss' || e2.estado === 'anulada')) {
        pa.fase = 'silencioso';
        pa.ativo = null;
        pa.proj = null;
        pa.lastBaseId = W.length ? W[W.length - 1].id : null;
        mudou = true;
      }
    }
    if (!mudou) break;
  }
}

/* ---------- BC: mesma ideia, com os 3 últimos brancos ---------- */
function calcBC(W, k) {
  if (k < 2) return null;
  const m = Math.round((mi(W[k].t) - mi(W[k - 2].t)) / 2);
  if (m <= 0) return null;
  return [1, 2, 3, 4].map((j) => mi(W[k].t) + j * m);
}
const novaProj = (W, k) => {
  const Ms = calcBC(W, k);
  return Ms ? { baseId: W[k].id, itens: Ms.map((M) => ({ M, estado: 'pendente', hitId: null })) } : null;
};

function stepBC(S, now) {
  const bc = S.bc;
  const W = brancos(S);
  for (let g = 0; g < 10; g++) {
    let mudou = false;
    if (bc.fase === 'silencioso') {
      const last = W[W.length - 1];
      if (bc.proj) {
        const p = bc.proj;
        let hit = null;
        for (const it of p.itens) {
          if (it.estado === 'pendente' && completa(S.stones, it.M, now)) {
            const h = acerto(S.stones, it.M);
            it.estado = h ? 'green' : 'loss';
            it.hitId = h ? h.id : null;
          }
          if (it.estado === 'green') {
            const h = W.find((w) => w.id === it.hitId);
            if (h && (!hit || h.t > hit.t)) hit = h;
          }
        }
        if (hit) {
          bc.fase = 'aguardando3'; bc.hitId = hit.id; bc.proj = null; bc.lote = null; mudou = true;
        } else if (p.itens.every((it) => it.estado !== 'pendente')) {
          bc.lastBaseId = p.baseId; bc.proj = null; mudou = true;
        } else if (last && last.id !== p.baseId) {
          // chegou um branco novo: larga o mais antigo e usa os 3 últimos (se nenhuma janela está aberta)
          const aberta = p.itens.some((it) => it.estado === 'pendente' && mi(now) >= it.M - 1);
          if (!aberta) {
            const np = novaProj(W, W.length - 1);
            if (np) { bc.proj = np; mudou = true; }
            else { bc.lastBaseId = last.id; bc.proj = null; }
          }
        }
      } else if (W.length >= 3 && last.id !== bc.lastBaseId) {
        const np = novaProj(W, W.length - 1);
        if (np) { bc.proj = np; mudou = true; }
        else bc.lastBaseId = last.id;
      }
    } else if (bc.fase === 'aguardando3') {
      // se alguma entrada do lote anterior acertar depois, vale o último acerto
      if (bc.lote) {
        for (const id of bc.lote) {
          const e = S.entradas.find((x) => x.id === id);
          if (e && e.estado === 'green') {
            const h = W.find((w) => w.id === e.hitId);
            const cur = W.find((w) => w.id === bc.hitId);
            if (h && cur && h.t > cur.t) bc.hitId = h.id;
          }
        }
      }
      const idx = W.findIndex((w) => w.id === bc.hitId);
      if (idx >= 0 && W.length - 1 - idx >= 3) {
        const Ms = calcBC(W, idx + 3);
        if (Ms) {
          bc.lote = Ms.map((M) => criar(S, 'BC', M, now).id);
          bc.fase = 'ativo';
          mudou = true;
        } else {
          bc.hitId = W[idx + 1].id; // mesma hora nos 3 brancos: avança a referência
          mudou = true;
        }
      }
    } else {
      // ativo: no primeiro acerto, já começa a esperar 3 brancos depois dele
      const lote = (bc.lote || []).map((id) => S.entradas.find((e) => e.id === id)).filter(Boolean);
      const acertos = lote.filter((e) => e.estado === 'green');
      if (acertos.length) {
        let h = null;
        for (const e of acertos) {
          const w = W.find((x) => x.id === e.hitId);
          if (w && (!h || w.t > h.t)) h = w;
        }
        if (h) { bc.fase = 'aguardando3'; bc.hitId = h.id; mudou = true; }
      } else if (lote.every((e) => e.estado !== 'pendente')) {
        bc.fase = 'silencioso'; bc.proj = null; bc.lote = null;
        bc.lastBaseId = W.length ? W[W.length - 1].id : null;
        mudou = true;
      }
    }
    if (!mudou) break;
  }
}

/* ---------- Wall: guarda 5 resultados de TODO branco; só aparece junto de outra estratégia ---------- */
// por branco: branco + pedra de trás, + pedra da frente, + 2 de trás, + 2 da frente, e a soma das 5
function stepWall(S, now) {
  const st = S.stones;
  const vivas = S.entradas.filter((e) => e.est !== 'W' && e.estado === 'pendente');
  if (!vivas.length) return;
  st.forEach((s, i) => {
    if (s.n !== 0 || i < 2 || i + 2 > st.length - 1) return;
    const p = [st[i - 1].n, st[i + 1].n, st[i - 2].n, st[i + 2].n];
    const soma = p.reduce((a, b) => a + b, 0);
    const T = mi(s.t);
    for (const v of [...p, soma]) {
      if (v <= 0) continue;
      const M = T + v;
      const key = `${s.id}-${M}`;
      if (S.wall.vistos[key] || M < mi(now) - 3) continue;
      if (vivas.some((e) => e.M === M)) {
        S.wall.vistos[key] = true;
        const ja = S.entradas.find((e) => e.est === 'W' && e.M === M && e.estado === 'pendente');
        if (ja) ja.cont = (ja.cont || 1) + 1; // outro branco caiu no mesmo horário: mais um W
        else { const w = criar(S, 'W', M, now); w.cont = 1; }
      }
    }
  });
}

/* ---------- Sequência antiga: valida entradas ativas das outras estratégias ---------- */
// Quando a próxima pedra cai dentro de 1 minuto (antes ou depois) de uma entrada ativa,
// as 5 últimas pedras (por cor) são procuradas no histórico: se esse padrão já veio antes
// de um branco, a entrada fica validada ("padrão" + data de quando aconteceu).
// Ajuste: CASAS = pedras observadas + o branco (6 = 5 pedras antes do branco).
export const SA_ATIVA = false; // standby: configurações guardadas, não participa de nada
export const CASAS = 6;
export const MIN_REPETICOES = 1;
const corDe = (n) => (n === 0 ? 'W' : n <= 7 ? 'R' : 'B');
function validarPadroes(S, now) {
  const st = S.stones;
  if (!SA_ATIVA || !S.consulta || st.length < CASAS - 1) return;
  const last = st[st.length - 1];
  if (S.sa.ultimoId === last.id) return;
  S.sa.ultimoId = last.id;
  const ult = st.slice(-(CASAS - 1));
  if (ult.some((x) => x.n === 0)) return;
  const Mprox = mi(last.t + 30000); // minuto previsto da próxima pedra
  const alvo = S.entradas.filter((e) => e.estado === 'pendente' && !e.padrao && Math.abs(e.M - Mprox) <= 1);
  if (!alvo.length) return;
  const r = S.consulta(ult.map((x) => corDe(x.n)).join(''));
  if (!r || r.count < MIN_REPETICOES) return;
  for (const e of alvo) e.padrao = { quando: r.quando, count: r.count, total: r.total };
}

/* ---------- força da entrada (pontuação pelas regras, não é chance real de acerto) ---------- */
// Base 39: 50% + 10% por PA, BC, Wall (cada um) e pela pedra 12 nos 3 min antes + 10% por x de devedor.
// PA/BC/Wall (sem Base 39): 50% + 15% por cada outra estratégia igual + 15% por x de devedor. Máximo 100%.
export function forca(ests, wc, dev, p12) {
  const hits = ests.reduce((a, k) => a + (k === 'W' ? wc || 1 : k === 'SA' ? 0 : 1), 0);
  const outros = Math.max(0, hits - 1);
  const d = dev || 0;
  const v = ests.includes('B39') ? 50 + 10 * outros + (p12 ? 10 : 0) + 10 * d : 50 + 15 * outros + 15 * d;
  return Math.min(100, v);
}

/* ---------- forte tendência e minuto mais forte ---------- */
function atualizarFlags(S, topDigito, dev) {
  const pend = S.entradas.filter((e) => e.estado === 'pendente');
  const porM = {};
  for (const e of pend) (porM[e.M] = porM[e.M] || []).push(e);
  for (const M in porM) {
    const fontes = [...new Set(porM[M].map((e) => e.est))];
    if (porM[M].some((e) => e.padrao)) fontes.push('SA');
    for (const e of porM[M]) {
      e.fontes = fontes;
      e.forte = fontes.length > 1;
      e.fogo = topDigito !== null && topDigito !== undefined && digitoDe(+M) === topDigito;
      e.p12 = e.est === 'B39' && S.stones.some((s) => s.n === 12 && mi(s.t) >= +M - 3 && mi(s.t) <= +M - 1); // pedra 12 nos 3 min antes
      e.dev = dev ? dev[Math.floor(new Date(+M * MIN).getMinutes() / 10) * 10] || 0 : 0; // casa devendo
    }
  }
}

// 3 finais de minuto em que mais saiu branco nas últimas 6 horas (não zera: a janela só desliza).
// brancos = horários (ms) em ordem crescente; anterior = ordem atual [d1,d2,d3] (quem empata fica onde está)
export const JANELA_TOP = 6 * 60 * MIN;
export function topMinutos(brancos, now, anterior = []) {
  const cont = {};
  for (const t of brancos) {
    if (t < now - JANELA_TOP) continue;
    const d = new Date(t).getMinutes() % 10;
    cont[d] = cont[d] || { d, c: 0, ult: 0 };
    cont[d].c++;
    cont[d].ult = Math.max(cont[d].ult, t);
  }
  const pos = (d) => { const i = anterior.indexOf(d); return i < 0 ? 99 : i; };
  return Object.values(cont).sort((a, b) => b.c - a.c || pos(a.d) - pos(b.d) || b.ult - a.ult).slice(0, 3);
}

/* ---------- passo principal ---------- */
// devolve as entradas que acabaram de ser resolvidas (para o relatório)
export function avancar(S, now, topDigito, dev, desligadas) {
  const novas = [];
  const off = new Set(desligadas || []); // estratégias ocultas = em standby
  for (const x of S.entradas) if (off.has(x.est) && x.estado === 'pendente') x.estado = 'anulada';
  atualizarFlags(S, topDigito, dev);
  for (let i = 0; i < 3; i++) {
    resolverTodas(S, now, novas);
    if (!off.has('B39')) stepB39(S, now);
    if (!off.has('PA')) stepPA(S, now);
    if (!off.has('BC')) stepBC(S, now);
    stepWall(S, now);
    validarPadroes(S, now);
  }
  resolverTodas(S, now, novas);
  atualizarFlags(S, topDigito, dev);
  return novas;
}

// o que aparece na tela (pendentes + resolvidas nos últimos 2 min)
export function visiveis(S, now) {
  return S.entradas.filter(
    (e) => e.estado === 'pendente' || (e.estado !== 'anulada' && e.resolvida && now - e.resolvida < 2 * MIN),
  );
}

// entradas que entram na janela de 2 minutos antes
export function alertas(S, now) {
  return S.entradas.filter(
    (e) => e.estado === 'pendente' && !e.alertado && now >= e.M * MIN - 2 * MIN && now < e.M * MIN,
  );
}
