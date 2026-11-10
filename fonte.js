// FONTE DAS PEDRAS: servidor próprio na nuvem (WebSocket).
// Troque a CHAVE_APP pela chave que você definiu no painel do servidor (variável CHAVE_APP).
export const SIMULADA = false;
export const SERVIDOR = 'wss://servidor-blaze.onrender.com';
export const CHAVE_APP = 'c4e4ba02ff4f493313adff1e799bed4a1222e9b89480b125';

let ws = null;
let timer = null;
let vigia = null;
let ativo = false;
let ultimaMsg = 0;
let tentativas = 0;
let cb = null;

function limpar() {
  clearTimeout(timer);
  clearInterval(vigia);
  timer = null;
  vigia = null;
  if (ws) {
    try { ws.onopen = ws.onmessage = ws.onerror = ws.onclose = null; ws.close(); } catch (e) {}
    ws = null;
  }
}

function agendar() {
  if (!ativo) return;
  clearTimeout(timer);
  tentativas++;
  timer = setTimeout(conectar, Math.min(5000 * tentativas, 15000)); // 5s, 10s, 15s...
}

// aceita {id, n, t}; descarta o que não for pedra válida (0 a 14)
function norm(m) {
  if (!m || m.n === undefined) return null;
  const n = Number(m.n);
  if (!(n >= 0 && n <= 14)) return null;
  const t = Number(m.t) || Date.now();
  return { id: Number(m.id) || t, n, t };
}

function conectar() {
  if (!ativo) return;
  limpar();
  try {
    ws = new WebSocket(`${SERVIDOR}/?chave=${encodeURIComponent(CHAVE_APP)}`);
  } catch (e) {
    cb.onStatus(false);
    agendar();
    return;
  }
  ws.onopen = () => {
    tentativas = 0;
    ultimaMsg = Date.now();
    cb.onStatus(true);
    // se o servidor ficar mudo por 50s, derruba e reconecta
    vigia = setInterval(() => {
      if (Date.now() - ultimaMsg > 50000) { try { ws && ws.close(); } catch (e) {} }
    }, 10000);
  };
  ws.onmessage = (ev) => {
    ultimaMsg = Date.now();
    let m;
    try { m = JSON.parse(ev.data); } catch (e) { return; }
    if (m.type === 'hb') return;
    if (m.type === 'inicial') {
      // a lista chega em qualquer ordem: coloca da mais antiga para a mais nova
      const lista = (m.lista || []).map(norm).filter(Boolean).sort((a, b) => a.t - b.t);
      cb.onInicial(lista);
      return;
    }
    const p = norm(m);
    if (p) cb.onNova(p);
  };
  ws.onerror = () => {};
  ws.onclose = () => {
    clearInterval(vigia);
    cb.onStatus(false);
    agendar();
  };
}

export function iniciarFonte({ onInicial, onNova, onStatus }) {
  cb = { onInicial, onNova, onStatus };
  ativo = true;
  tentativas = 0;
  conectar();
}

export function pararFonte() {
  ativo = false;
  limpar();
  if (cb) cb.onStatus(false);
}
