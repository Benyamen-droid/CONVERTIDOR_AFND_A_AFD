const EXAMPLES = {
  ends01: { dir:'toDfa', name:'cadenas que terminan en 01', start:'q0', finals:'q2', trans:'q0 0 q0 q1\nq0 1 q0\nq1 1 q2' },
  dragon: { dir:'toDfa', name:'(a|b)*abb con transiciones ε', start:'q0', finals:'q10', trans:
    'q0 ε q1 q7\nq1 ε q2 q4\nq2 a q3\nq4 b q5\nq3 ε q6\nq5 ε q6\nq6 ε q1 q7\nq7 a q8\nq8 b q9\nq9 b q10' },
  penult: { dir:'toDfa', name:'penúltimo símbolo es a', start:'p', finals:'r', trans:'p a p q\np b p\nq a r\nq b r' },
  evenA: { dir:'toNfa', name:'número par de a', start:'q0', finals:'q0', trans:'q0 a q1\nq0 b q0\nq1 a q0\nq1 b q1' },
  startA: { dir:'toNfa', name:'empiezan con a', start:'q0', finals:'q1', trans:'q0 a q1\nq0 b qe\nq1 a q1\nq1 b q1\nqe a qe\nqe b qe' }
};
const EPS = new Set(['ε','eps','epsilon','λ','&','lambda']);
const $ = id => document.getElementById(id);
const esc = s => String(s).replace(/[&<>"]/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;'}[c]));
const tokens = v => v.replace(/[,;{}]/g,' ').split(/\s+/).filter(Boolean);
const normSym = a => (EPS.has(a) || EPS.has(a.toLowerCase())) ? 'ε' : a;
const fmtSet = arr => arr.length ? '{' + arr.join(', ') + '}' : '∅';
function toast(msg) { const t=$('toast'); t.textContent=msg; t.hidden=false; clearTimeout(toast.t); toast.t=setTimeout(()=>t.hidden=true,1800); }


/* ---------- Estructura y algoritmos ---------- */
function parseText(text, start, finalsStr) {
  const states=[], delta=new Map(), alpha=[]; let hasEps=false;
  const add = s => { if (!delta.has(s)) { delta.set(s,new Map()); states.push(s); } };
  add(start);
  text.split('\n').forEach(line => {
    const t = tokens(line.trim()); if (t.length < 2) return;
    const [from, rawSym, ...tos] = t, sym = normSym(rawSym);
    add(from); tos.forEach(add);
    if (sym==='ε') hasEps=true; else if (!alpha.includes(sym)) alpha.push(sym);
    const m = delta.get(from); if (!m.has(sym)) m.set(sym,new Set());
    tos.forEach(x => m.get(sym).add(x));
  });
  const finals = new Set(tokens(finalsStr)); finals.forEach(add);
  return { states, alpha, delta, start, finals, hasEps };
}
function analyze(p) {
  const reasons=[];
  if (p.hasEps) reasons.push('tiene transiciones ε');
  p.states.forEach(s => p.delta.get(s).forEach((t,a) => { if (a!=='ε' && t.size>1) reasons.push(`desde ${s} con ${a} hay ${t.size} destinos`); }));
  let missing=0;
  p.states.forEach(s => p.alpha.forEach(a => { if (!p.delta.get(s).get(a)?.size) missing++; }));
  return { det:!reasons.length, reasons, missing };
}
function closure(nfa, set) {
  const out=new Set(set), stack=[...set];
  while (stack.length) { const q=stack.pop(); nfa.delta.get(q)?.get('ε')?.forEach(p => { if (!out.has(p)) { out.add(p); stack.push(p); } }); }
  return out;
}
function move(nfa, set, a) { const out=new Set(); set.forEach(q => nfa.delta.get(q)?.get(a)?.forEach(p => out.add(p))); return out; }
function subsetConstruction(nfa) {
  const idx = new Map(nfa.states.map((s,i)=>[s,i]));
  const sortSet = S => [...S].sort((a,b)=>idx.get(a)-idx.get(b));
  const dstates=[], byKey=new Map(); let letter=0;
  const add = S => {
    const arr=sortSet(S), k=arr.join('\u0001');
    if (byKey.has(k)) return byKey.get(k);
    const L='ABCDEFGHIJKLMNOPQRSTUVWXYZ', n=letter++;
    const d = { id:dstates.length, set:arr, trap:!arr.length, final:arr.some(q=>nfa.finals.has(q)), trans:{},
      name: arr.length ? (n<26 ? L[n] : L[n%26]+Math.floor(n/26)) : '∅' };
    if (!arr.length) letter--;
    byKey.set(k,d); dstates.push(d); return d;
  };
  add(closure(nfa, new Set([nfa.start])));
  for (let i=0;i<dstates.length;i++) for (const a of nfa.alpha) dstates[i].trans[a] = add(closure(nfa, move(nfa, dstates[i].set, a))).id;
  return { states:dstates, alpha:nfa.alpha, start:0 };
}
const FULL_MAX = 5;
function fullSubsetModel(nfa, dfa) {
  const n=nfa.states.length, idx=new Map(nfa.states.map((s,i)=>[s,i]));
  const keyOf = S => [...S].sort((a,b)=>idx.get(a)-idx.get(b)).join('\u0001');
  const subsets=[]; for (let m=0;m<(1<<n);m++) subsets.push(nfa.states.filter((_,i)=>m>>i&1));
  subsets.sort((a,b)=>a.length-b.length);
  const id=new Map(subsets.map((s,i)=>[s.join('\u0001'),String(i)]));
  const letter=new Map(dfa.states.map(d=>[d.set.join('\u0001'),d.name]));
  const start=id.get(keyOf(closure(nfa,new Set([nfa.start]))));
  const trans=subsets.map(S=>Object.fromEntries(nfa.alpha.map(a=>[a,id.get(keyOf(closure(nfa,move(nfa,S,a))))])));
  const reach=new Set([start]), st=[start];
  while (st.length) { const q=st.pop(); Object.values(trans[+q]).forEach(t=>{ if(!reach.has(t)){reach.add(t);st.push(t);} }); }
  const nodes=subsets.map((S,i)=>{ const k=String(i), ok=reach.has(k);
    return { id:k, label:S.length?'{'+S.join(',')+'}':'∅', final:S.some(q=>nfa.finals.has(q)), cls:ok?'':'gone',
      sub: ok ? (S.length ? '= '+letter.get(S.join('\u0001')) : 'error') : 'eliminado' }; });
  const edges=new Map();
  subsets.forEach((S,i)=>nfa.alpha.forEach(a=>{
    const f=String(i), t=trans[i][a], k=f+'\u0001'+t;
    if (!edges.has(k)) edges.set(k,{from:f,to:t,syms:[],cls:reach.has(f)?'':'gone'});
    edges.get(k).syms.push(a);
  }));
  return { model:{ nodes, start, edges:[...edges.values()].map(e=>({from:e.from,to:e.to,label:e.syms.join(', '),cls:e.cls})) },
    total:subsets.length, reachable:reach.size };
}

/* ---------- Dibujo ---------- */
function nodeRadius(label) { return Math.max(22, 9 + label.length*4.2); }
function autoLayout(model) {
  const level=new Map([[model.start,0]]), q=[model.start], order=[model.start];
  while (q.length) { const s=q.shift(); for (const e of model.edges) if (e.from===s && !level.has(e.to)) { level.set(e.to,level.get(s)+1); q.push(e.to); order.push(e.to); } }
  const maxL=Math.max(0,...level.values());
  const unreached=model.nodes.filter(n=>!level.has(n.id)).map(n=>n.id);
  const cols=new Map();
  order.forEach(id=>{ const l=level.get(id); if(!cols.has(l)) cols.set(l,[]); cols.get(l).push(id); });
  const pos={}, maxRows=Math.max(...[...cols.values()].map(c=>c.length)), DX=150, DY=115;
  cols.forEach((ids,l)=>ids.forEach((id,r)=>{ pos[id]={x:70+l*DX, y:80+(r-(ids.length-1)/2)*DY+(maxRows-1)/2*DY}; }));
  if (unreached.length) {
    const perRow=Math.max(4,maxL+1), baseY=Math.max(...Object.values(pos).map(p=>p.y))+170;
    unreached.forEach((id,i)=>pos[id]={x:70+(i%perRow)*DX, y:baseY+Math.floor(i/perRow)*135});
  }
  return pos;
}
function automatonMarkup(model, pos, opts, uid) {
  const hlN=new Set(opts.hlNodes||[]), hlE=new Set(opts.hlEdges||[]), src=opts.src;
  let out=`<defs><marker id="ah-${uid}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto-start-reverse"><path class="arrowhead" d="M0,0 L10,5 L0,10 z"/></marker>
    <marker id="as-${uid}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="8" markerHeight="8" orient="auto"><path class="arrowstart" d="M0,0 L10,5 L0,10 z"/></marker></defs>`;
  const R={}; model.nodes.forEach(n=>R[n.id]=nodeRadius(n.label));
  const pairs=new Set(model.edges.map(e=>e.from+'\u0001'+e.to));
  for (const e of model.edges) {
    const p1=pos[e.from], p2=pos[e.to], r1=R[e.from], r2=R[e.to];
    if (!p1||!p2) continue;
    let d,lx,ly;
    if (e.from===e.to) {
      const a1=-Math.PI/2-0.55, a2=-Math.PI/2+0.55, hgt=r1+38;
      const sx=p1.x+r1*Math.cos(a1), sy=p1.y+r1*Math.sin(a1), ex=p1.x+r1*Math.cos(a2), ey=p1.y+r1*Math.sin(a2);
      d=`M${sx},${sy} C${p1.x-r1-4},${p1.y-hgt} ${p1.x+r1+4},${p1.y-hgt} ${ex},${ey}`; lx=p1.x; ly=p1.y-r1-36;
    } else {
      const dx=p2.x-p1.x, dy=p2.y-p1.y, dist=Math.hypot(dx,dy)||1, nx=-dy/dist, ny=dx/dist;
      let off=pairs.has(e.to+'\u0001'+e.from)?30:0;
      if (!off) for (const n of model.nodes) {
        if (n.id===e.from||n.id===e.to) continue;
        const p=pos[n.id]; if(!p) continue;
        const t=((p.x-p1.x)*dx+(p.y-p1.y)*dy)/(dist*dist);
        if (t>0&&t<1&&Math.abs((p.x-p1.x)*nx+(p.y-p1.y)*ny)<R[n.id]+6) { off=55; break; }
      }
      const cx=(p1.x+p2.x)/2+nx*off*2, cy=(p1.y+p2.y)/2+ny*off*2;
      const u1x=cx-p1.x,u1y=cy-p1.y,l1=Math.hypot(u1x,u1y)||1,u2x=cx-p2.x,u2y=cy-p2.y,l2=Math.hypot(u2x,u2y)||1;
      const sx=p1.x+u1x/l1*r1, sy=p1.y+u1y/l1*r1, ex=p2.x+u2x/l2*(r2+1), ey=p2.y+u2y/l2*(r2+1);
      d=`M${sx},${sy} Q${cx},${cy} ${ex},${ey}`; lx=0.25*sx+0.5*cx+0.25*ex; ly=0.25*sy+0.5*cy+0.25*ey;
    }
    const tw=e.label.length*7.4+10, k=e.from+'\u0001'+e.to;
    out+=`<g class="edge${e.eps?' eps':''}${e.cls?' '+e.cls:''}${hlE.has(k)?' hl':''}" data-from="${esc(e.from)}" data-to="${esc(e.to)}"><path d="${d}" marker-end="url(#ah-${uid})"/>`+
      `<rect x="${lx-tw/2}" y="${ly-10}" width="${tw}" height="20" rx="4"/><text x="${lx}" y="${ly}">${esc(e.label)}</text></g>`;
  }
  const sp=pos[model.start], sr=R[model.start];
  if (sp) out+=`<polygon class="starttri" points="${sp.x-sr},${sp.y} ${sp.x-sr-22},${sp.y-12} ${sp.x-sr-22},${sp.y+12}"/>`;
  for (const n of model.nodes) {
    const p=pos[n.id], r=R[n.id]; if(!p) continue;
    out+=`<g class="node${n.trap?' trap':''}${n.cls?' '+n.cls:''}${hlN.has(n.id)?' hl':''}${src===n.id?' src':''}" data-id="${esc(n.id)}"><circle class="outer" cx="${p.x}" cy="${p.y}" r="${r}"/>`;
    if (n.final) out+=`<circle cx="${p.x}" cy="${p.y}" r="${r-4.5}" style="fill:none"/>`;
    out+=`<text class="name" x="${p.x}" y="${p.y}">${esc(n.label)}</text>`;
    if (n.sub) out+=`<text class="subset" x="${p.x}" y="${p.y+r+14}">${esc(n.sub)}</text>`;
    out+='</g>';
  }
  return out;
}
function toSvg(svg, ev) { const pt=svg.createSVGPoint(); pt.x=ev.clientX; pt.y=ev.clientY; return pt.matrixTransform(svg.getScreenCTM().inverse()); }
// El SVG se ajusta (viewBox) al espacio disponible: aprovecha todo el panel sin scroll.
function drawAutomaton(box, model) {
  const pos=autoLayout(model);
  const svg=document.createElementNS('http://www.w3.org/2000/svg','svg');
  svg.setAttribute('preserveAspectRatio','xMidYMid meet');
  const render=()=>{
    const xs=Object.values(pos).map(p=>p.x), ys=Object.values(pos).map(p=>p.y);
    const minX=Math.min(...xs)-80, minY=Math.min(...ys)-80, w=Math.max(...xs)+80-minX, h=Math.max(...ys)+90-minY;
    svg.setAttribute('viewBox',`${minX} ${minY} ${w} ${h}`);
    svg.innerHTML=automatonMarkup(model,pos,{},'out'+box.id);
  };
  render();
  let drag=null;
  svg.addEventListener('pointerdown', ev=>{ const g=ev.target.closest('.node'); if(!g) return; const id=g.dataset.id, pt=toSvg(svg,ev);
    drag={id,dx:pos[id].x-pt.x,dy:pos[id].y-pt.y}; try{svg.setPointerCapture(ev.pointerId);}catch(e){} ev.preventDefault(); });
  svg.addEventListener('pointermove', ev=>{ if(!drag) return; const pt=toSvg(svg,ev); pos[drag.id]={x:pt.x+drag.dx,y:pt.y+drag.dy}; render(); });
  svg.addEventListener('pointerup',()=>drag=null); svg.addEventListener('pointercancel',()=>drag=null);
  box.replaceChildren(svg);
}
function structModel(p) {
  const edges=new Map();
  p.states.forEach(s=>p.delta.get(s).forEach((tos,sym)=>tos.forEach(t=>{ const k=s+'\u0001'+t; if(!edges.has(k)) edges.set(k,{from:s,to:t,syms:[]}); edges.get(k).syms.push(sym); })));
  return { nodes:p.states.map(s=>({id:s,label:s,final:p.finals.has(s)})), start:p.start,
    edges:[...edges.values()].map(e=>({from:e.from,to:e.to,label:e.syms.join(', '),eps:e.syms.every(x=>x==='ε')})) };
}
function dfaModel(dfa) {
  const edges=new Map();
  dfa.states.forEach(s=>dfa.alpha.forEach(a=>{ const t=s.trans[a], k=s.id+'\u0001'+t; if(!edges.has(k)) edges.set(k,{from:String(s.id),to:String(t),syms:[]}); edges.get(k).syms.push(a); }));
  return { nodes:dfa.states.map(s=>({id:String(s.id),label:s.name,final:s.final,trap:s.trap,sub:s.trap?'':'{'+s.set.join(',')+'}'})),
    start:String(dfa.start), edges:[...edges.values()].map(e=>({from:e.from,to:e.to,label:e.syms.join(', ')})) };
}

/* ---------- Tablas ---------- */
const mark=(isStart,isFinal)=>`<span class="marks">${isStart?'<span class="m-s">→</span>':''}${isFinal?'<span class="m-f">*</span>':''}</span>`;
function nfaTable(p) {
  const cols=[...p.alpha,...(p.hasEps?['ε']:[])];
  let h='<table><thead><tr><th></th><th>δ</th>'+cols.map(c=>`<th>${esc(c)}</th>`).join('')+'</tr></thead><tbody>';
  p.states.forEach(s=>{ h+=`<tr><td>${mark(s===p.start,p.finals.has(s))}</td><td class="st">${esc(s)}</td>`+cols.map(c=>{ const t=p.delta.get(s).get(c); return t&&t.size?`<td>${esc(fmtSet([...t]))}</td>`:'<td class="empty">∅</td>'; }).join('')+'</tr>'; });
  return h+'</tbody></table>';
}
function detTable(p) {
  let h='<table><thead><tr><th></th><th>δ</th>'+p.alpha.map(a=>`<th>${esc(a)}</th>`).join('')+'</tr></thead><tbody>';
  p.states.forEach(s=>{ h+=`<tr><td>${mark(s===p.start,p.finals.has(s))}</td><td class="st">${esc(s)}</td>`+p.alpha.map(a=>{ const t=p.delta.get(s).get(a); return t&&t.size?`<td>${esc([...t][0])}</td>`:'<td class="empty">—</td>'; }).join('')+'</tr>'; });
  return h+'</tbody></table>';
}
function dfaTable(dfa) {
  let h='<table><thead><tr><th></th><th>δ</th><th>Estados del AFND</th>'+dfa.alpha.map(a=>`<th>${esc(a)}</th>`).join('')+'</tr></thead><tbody>';
  dfa.states.forEach(s=>{ h+=`<tr><td>${mark(s.id===dfa.start,s.final)}</td><td class="st">${esc(s.name)}</td><td><span class="set">${esc(fmtSet(s.set))}</span></td>`+dfa.alpha.map(a=>`<td>${esc(dfa.states[s.trans[a]].name)}</td>`).join('')+'</tr>'; });
  return h+'</tbody></table>';
}

/* ---------- Conversión y pestañas ---------- */
function setTag(id,kind){ const t=$(id); t.className='tag '+(kind==='AFD'?'dfa':'nfa'); t.textContent=kind; }
function selectTab(which) {
  const full = which==='full';
  $('tabOut').setAttribute('aria-selected', String(!full)); $('tabFull').setAttribute('aria-selected', String(full));
  $('paneOut').hidden = full; $('paneFull').hidden = !full;
}
$('tabOut').addEventListener('click',()=>selectTab('out'));
$('tabFull').addEventListener('click',()=>selectTab('full'));

function showConversion(dir, p, label) {
  selectTab('out');
  if (dir==='toDfa') {
    const dfa=subsetConstruction(p), hasTrap=dfa.states.some(s=>s.trap);
    $('resTitle').textContent='AFND → AFD';
    $('topNote').innerHTML=`${label?'<b>'+esc(label)+'.</b> ':''}AFND de ${p.states.length} estados → AFD de ${dfa.states.length} estados${hasTrap?' (incluye estado de error ∅)':''}.`;
    setTag('inTag','AFND'); setTag('outTag','AFD');
    $('tblIn').innerHTML=nfaTable(p); $('tblOut').innerHTML=dfaTable(dfa);
    drawAutomaton($('svgOut'), dfaModel(dfa));
    $('legendExtra').textContent='Bajo cada estado: los estados del AFND que agrupa';
    $('tabFull').hidden=false;
    const n=p.states.length;
    if (n<=FULL_MAX) {
      const full=fullSubsetModel(p,dfa), gone=full.total-full.reachable;
      $('fullNote').textContent=`2^${n} = ${full.total} subconjuntos de {${p.states.join(', ')}}: ${full.reachable} alcanzables (forman el AFD)`+(gone?`, ${gone} inalcanzables (se eliminan).`:'.');
      drawAutomaton($('svgFull'), full.model);
    } else {
      $('fullNote').textContent=`Con ${n} estados habría 2^${n} = ${2**n} subconjuntos: demasiados para dibujarlos (máximo ${FULL_MAX} estados).`;
      $('svgFull').replaceChildren();
    }
  } else {
    const info=analyze(p);
    $('resTitle').textContent='AFD → AFND';
    $('topNote').innerHTML=`${label?'<b>'+esc(label)+'.</b> ':''}Cada δ(q,a)=p pasa a δ(q,a)={p}. `+(info.missing?`Las ${info.missing} casillas vacías quedan como ∅.`:'Estados, inicial y finales no cambian.');
    setTag('inTag','AFD'); setTag('outTag','AFND');
    $('tblIn').innerHTML=detTable(p); $('tblOut').innerHTML=nfaTable(p);
    drawAutomaton($('svgOut'), structModel(p));
    $('legendExtra').textContent='';
    $('tabFull').hidden=true;
  }
}

/* ---------- Editor gráfico ---------- */
const ED={states:[],trans:new Map(),start:null,finals:new Set(),nextId:0,tool:'state',sel:null,pending:null,menuFor:null,linkFrom:null};
const edSvg=$('edSvg'), edCanvas=$('edCanvas');
const EK=(f,t)=>f+'\u0001'+t;
const stById=id=>ED.states.find(s=>s.id===id);
function edModel() {
  return { nodes:ED.states.map(s=>({id:String(s.id),label:s.name,final:ED.finals.has(s.id)})),
    start:ED.start==null?null:String(ED.start),
    edges:[...ED.trans.entries()].map(([k,syms])=>{ const [f,t]=k.split('\u0001'); return {from:f,to:t,label:[...syms].join(', '),eps:[...syms].every(x=>x==='ε')}; }) };
}
function edToStruct() {
  const name=id=>stById(id).name;
  const states=ED.states.map(s=>s.name), delta=new Map(states.map(s=>[s,new Map()])), alpha=[]; let hasEps=false;
  ED.trans.forEach((syms,k)=>{ const [f,t]=k.split('\u0001').map(Number);
    syms.forEach(a=>{ if(a==='ε') hasEps=true; else if(!alpha.includes(a)) alpha.push(a);
      const m=delta.get(name(f)); if(!m.has(a)) m.set(a,new Set()); m.get(a).add(name(t)); }); });
  return { states, alpha, delta, hasEps, start:ED.start==null?'':name(ED.start), finals:new Set([...ED.finals].map(name)) };
}
function edLoadStruct(p) {
  const pos=autoLayout(structModel(p));
  const xs=p.states.map(s=>pos[s].x), ys=p.states.map(s=>pos[s].y);
  const minX=Math.min(...xs), minY=Math.min(...ys), w=Math.max(...xs)-minX||1, h=Math.max(...ys)-minY||1;
  const W=edCanvas.clientWidth||Math.max(innerWidth-330,400), H=edCanvas.clientHeight||Math.max(innerHeight-70,340);
  const k=Math.max(0.5,Math.min(1,(W-180)/w,(H-200)/h));
  ED.states=[]; ED.trans=new Map(); ED.finals=new Set(); ED.nextId=0; ED.sel=null; ED.linkFrom=null;
  const ids=new Map();
  p.states.forEach(s=>{ const id=ED.nextId++; ids.set(s,id); ED.states.push({id,name:s,x:100+(pos[s].x-minX)*k,y:110+(pos[s].y-minY)*k}); });
  p.states.forEach(s=>p.delta.get(s).forEach((t,a)=>t.forEach(x=>{ const key=EK(ids.get(s),ids.get(x)); if(!ED.trans.has(key)) ED.trans.set(key,new Set()); ED.trans.get(key).add(a); })));
  ED.start=ids.has(p.start)?ids.get(p.start):null;
  p.finals.forEach(f=>ids.has(f)&&ED.finals.add(ids.get(f)));
}
function edParseSyms(v){ const t=tokens(v).map(normSym); return t.length?[...new Set(t)]:['ε']; }
function edAddTrans(from,to,syms){ const k=EK(from,to), set=ED.trans.get(k)||new Set(); syms.forEach(a=>set.add(a)); ED.trans.set(k,set); ED.sel={type:'edge',from,to}; }
function edHint() {
  if (ED.linkFrom!=null) return `Origen: ${stById(ED.linkFrom)?.name}. Haz clic en el estado destino (o en el mismo para un bucle). Esc cancela.`;
  return { select:'Arrastra los estados para moverlos. Clic para editar. Doble clic alterna final.',
    state:'Clic en el lienzo para crear un estado. Luego usa → Transición para unirlos.',
    trans:'Clic en el estado origen y luego en el destino, o arrastra de uno a otro.',
    delete:'Clic sobre un estado o una etiqueta de transición para borrarlo.' }[ED.tool];
}
function edRender(temp) {
  const pos={}; ED.states.forEach(s=>pos[String(s.id)]={x:s.x,y:s.y});
  let m=automatonMarkup(edModel(),pos,{ hlNodes:ED.sel?.type==='state'?[String(ED.sel.id)]:[], hlEdges:ED.sel?.type==='edge'?[EK(ED.sel.from,ED.sel.to)]:[], src:ED.linkFrom==null?null:String(ED.linkFrom) },'ed');
  if (temp) m+=`<line class="temp" x1="${temp.x1}" y1="${temp.y1}" x2="${temp.x2}" y2="${temp.y2}"/>`;
  edSvg.innerHTML=m; $('edEmpty').hidden=ED.states.length>0; $('edHint').textContent=edHint();
  if (!temp) edSide();
}
function edSide() {
  const p=edToStruct(), info=analyze(p), type=$('edType');
  type.hidden=!ED.states.length; type.className='ed-type '+(info.det?'dfa':'nfa');
  type.textContent=info.det?(info.missing?'AFD parcial':'AFD'):'AFND';
  let msg='';
  if (!ED.states.length) msg='Crea al menos un estado.';
  else if (ED.start==null) msg='Marca un estado inicial (clic derecho sobre un estado).';
  else if (!p.alpha.length) msg='Agrega transiciones con algún símbolo.';
  else if (!p.finals.size) msg='Aún no hay estados finales (doble clic o clic derecho).';
  else if (info.det) msg=`Es un AFD${info.missing?` parcial (faltan ${info.missing} transiciones)`:''}. Se puede convertir en ambas direcciones.`;
  else msg=`Es un AFND: ${info.reasons[0]}. Conviértelo con AFND → AFD.`;
  $('edMsg').textContent=msg;
  const ready=ED.states.length&&ED.start!=null&&p.alpha.length;
  $('edToDfa').disabled=!ready; $('edToNfa').disabled=!ready||!info.det;
  $('edToNfa').title=info.det?'':'Solo disponible cuando el autómata es determinista';
  const opts=ED.states.map(s=>`<option value="${s.id}">${esc(s.name)}</option>`).join('');
  const kf=$('edFrom').value, kt=$('edTo').value;
  $('edFrom').innerHTML=opts; $('edTo').innerHTML=opts;
  if (stById(+kf)) $('edFrom').value=kf;
  if (stById(+kt)) $('edTo').value=kt; else if (ED.states.length>1) $('edTo').value=ED.states[1].id;
  $('edAddBox').hidden=!ED.states.length;
  const props=$('edProps');
  if (ED.sel?.type==='state'&&stById(ED.sel.id)) {
    const s=stById(ED.sel.id);
    props.innerHTML=`<div class="ed-box"><h3>Estado ${esc(s.name)}</h3>
      <div><label class="lbl" for="edName">Nombre</label><input type="text" id="edName" value="${esc(s.name)}" spellcheck="false"></div>
      <label class="chk"><input type="checkbox" id="edIsStart" ${ED.start===s.id?'checked':''}> Estado inicial</label>
      <label class="chk"><input type="checkbox" id="edIsFinal" ${ED.finals.has(s.id)?'checked':''}> Estado final</label>
      <div><button id="edDelSel">Borrar estado</button></div></div>`;
    $('edName').addEventListener('change',e=>edRename(s.id,e.target.value.trim()));
    $('edIsStart').addEventListener('change',e=>{ ED.start=e.target.checked?s.id:(ED.start===s.id?null:ED.start); edRender(); });
    $('edIsFinal').addEventListener('change',e=>{ e.target.checked?ED.finals.add(s.id):ED.finals.delete(s.id); edRender(); });
    $('edDelSel').addEventListener('click',()=>edDeleteState(s.id));
  } else if (ED.sel?.type==='edge'&&ED.trans.has(EK(ED.sel.from,ED.sel.to))) {
    const {from,to}=ED.sel;
    props.innerHTML=`<div class="ed-box"><h3>Transición ${esc(stById(from).name)} → ${esc(stById(to).name)}</h3>
      <div><label class="lbl" for="edEdgeSyms">Símbolos (vacío = ε)</label><input type="text" id="edEdgeSyms" value="${esc([...ED.trans.get(EK(from,to))].join(', '))}" spellcheck="false"></div>
      <div style="display:flex;gap:6px;flex-wrap:wrap"><button class="primary" id="edEdgeSave">Guardar</button><button id="edDelSel">Borrar transición</button></div></div>`;
    const save=()=>{ ED.trans.set(EK(from,to),new Set(edParseSyms($('edEdgeSyms').value))); edRender(); };
    $('edEdgeSave').addEventListener('click',save);
    $('edEdgeSyms').addEventListener('keydown',e=>{ if(e.key==='Enter') save(); });
    $('edDelSel').addEventListener('click',()=>edDeleteEdge(from,to));
  } else props.innerHTML='';
  $('edTable').innerHTML=ED.states.length?nfaTable(p):'<p class="hint" style="padding:8px">Aparecerá cuando crees estados.</p>';
}
function edAddState(x,y){ let i=0; while(ED.states.some(s=>s.name==='q'+i)) i++; const s={id:ED.nextId++,name:'q'+i,x,y}; ED.states.push(s); if(ED.start==null) ED.start=s.id; ED.sel={type:'state',id:s.id}; edRender(); }
function edDeleteState(id){
  ED.states=ED.states.filter(s=>s.id!==id);
  [...ED.trans.keys()].forEach(k=>{ const [f,t]=k.split('\u0001').map(Number); if(f===id||t===id) ED.trans.delete(k); });
  ED.finals.delete(id); if(ED.start===id) ED.start=ED.states.length?ED.states[0].id:null; if(ED.linkFrom===id) ED.linkFrom=null;
  ED.sel=null; edRender();
}
function edDeleteEdge(f,t){ ED.trans.delete(EK(f,t)); ED.sel=null; edRender(); }
function edRename(id,n){
  if (!n||/[\s,;{}#]/.test(n)||n==='∅'||ED.states.some(s=>s.id!==id&&s.name===n)) { toast('Nombre no válido o repetido'); return edRender(); }
  stById(id).name=n; edRender();
}
function hideEdPopups(){ $('edPop').hidden=true; $('edMenu').hidden=true; ED.pending=null; }
function canvasPoint(ev){ const r=edCanvas.getBoundingClientRect(); return {x:ev.clientX-r.left,y:ev.clientY-r.top}; }
function placeBox(el,x,y,w,h){ el.style.left=Math.max(8,Math.min(x,edCanvas.clientWidth-w-8))+'px'; el.style.top=Math.max(8,Math.min(y,edCanvas.clientHeight-h-8))+'px'; }
function openSymPopup(from,to){
  const a=stById(from), b=stById(to);
  ED.linkFrom=null; ED.pending={from,to}; edRender();
  $('edPopLbl').textContent=`Símbolo(s) de ${a.name} → ${b.name}`;
  const pop=$('edPop'); pop.hidden=false;
  placeBox(pop,(a.x+b.x)/2-125,(a.y+b.y)/2-(from===to?150:65),250,150);
  $('edSym').value=''; $('edSym').focus();
}
function setTool(t){
  ED.tool=t; ED.linkFrom=null;
  document.querySelectorAll('[data-tool]').forEach(b=>b.setAttribute('aria-pressed',String(b.dataset.tool===t)));
  edCanvas.className='ed-canvas tool-'+t; edRender();
}
document.querySelectorAll('[data-tool]').forEach(b=>b.addEventListener('click',()=>setTool(b.dataset.tool)));

let edDrag=null;
edSvg.addEventListener('pointerdown',ev=>{
  if (ev.button===2) return;
  hideEdPopups();
  const pt=toSvg(edSvg,ev), g=ev.target.closest('.node'), eg=ev.target.closest('.edge'), nodeId=g?+g.dataset.id:null;
  if (ED.tool==='delete') { if(g) edDeleteState(nodeId); else if(eg) edDeleteEdge(+eg.dataset.from,+eg.dataset.to); return; }
  if (ED.tool==='trans'||ED.linkFrom!=null) {
    if (!g) { ED.linkFrom=null; edRender(); return; }
    edDrag={kind:'trans',from:nodeId,x0:pt.x,y0:pt.y,moved:false};
    try{edSvg.setPointerCapture(ev.pointerId);}catch(e){} ev.preventDefault(); return;
  }
  if (ED.tool==='state'&&!g&&!eg) { edAddState(pt.x,pt.y); return; }
  if (g) { const s=stById(nodeId); ED.sel={type:'state',id:nodeId}; edDrag={kind:'move',id:nodeId,dx:s.x-pt.x,dy:s.y-pt.y};
    try{edSvg.setPointerCapture(ev.pointerId);}catch(e){} ev.preventDefault(); }
  else if (eg) ED.sel={type:'edge',from:+eg.dataset.from,to:+eg.dataset.to};
  else ED.sel=null;
  edRender();
});
edSvg.addEventListener('pointermove',ev=>{
  const pt=toSvg(edSvg,ev);
  if (!edDrag) { if (ED.linkFrom!=null) { const s=stById(ED.linkFrom); edRender({x1:s.x,y1:s.y,x2:pt.x,y2:pt.y}); } return; }
  if (edDrag.kind==='move') {
    const s=stById(edDrag.id);
    s.x=Math.max(30,Math.min(pt.x+edDrag.dx,edCanvas.clientWidth-30)); s.y=Math.max(30,Math.min(pt.y+edDrag.dy,edCanvas.clientHeight-30));
    edRender({x1:s.x,y1:s.y,x2:s.x,y2:s.y});
  } else {
    if (Math.hypot(pt.x-edDrag.x0,pt.y-edDrag.y0)>8) edDrag.moved=true;
    const s=stById(ED.linkFrom??edDrag.from); edRender({x1:s.x,y1:s.y,x2:pt.x,y2:pt.y});
  }
});
edSvg.addEventListener('pointerup',ev=>{
  if (!edDrag) return;
  const d=edDrag; edDrag=null;
  if (d.kind==='move') { edRender(); return; }
  edRender();
  const hitEl=document.elementFromPoint(ev.clientX,ev.clientY)?.closest('#edSvg .node'), hit=hitEl?+hitEl.dataset.id:null;
  if (ED.linkFrom!=null) { if(hit!=null) openSymPopup(ED.linkFrom,hit); else { ED.linkFrom=null; edRender(); } }
  else if (d.moved) { if(hit!=null) openSymPopup(d.from,hit); }
  else { ED.linkFrom=d.from; edRender(); }
});
edSvg.addEventListener('pointercancel',()=>{ edDrag=null; edRender(); });
edSvg.addEventListener('dblclick',ev=>{ const g=ev.target.closest('.node'); if(!g||ED.tool!=='select') return; const id=+g.dataset.id; ED.finals.has(id)?ED.finals.delete(id):ED.finals.add(id); edRender(); });
edSvg.addEventListener('contextmenu',ev=>{
  ev.preventDefault(); const g=ev.target.closest('.node'); if(!g) return;
  hideEdPopups(); ED.menuFor=+g.dataset.id; ED.sel={type:'state',id:ED.menuFor}; edRender();
  const menu=$('edMenu'), p=canvasPoint(ev); menu.hidden=false; placeBox(menu,p.x,p.y,190,190);
});
$('edMenu').addEventListener('click',e=>{
  const b=e.target.closest('[data-act]'); if(!b) return;
  const id=ED.menuFor; $('edMenu').hidden=true;
  if (b.dataset.act==='link') { ED.linkFrom=id; return edRender(); }
  if (b.dataset.act==='start') ED.start=id;
  else if (b.dataset.act==='final') ED.finals.has(id)?ED.finals.delete(id):ED.finals.add(id);
  else if (b.dataset.act==='del') return edDeleteState(id);
  edRender();
  if (b.dataset.act==='rename') { $('edName').focus(); $('edName').select(); }
});
function confirmSymPopup(){ const pd=ED.pending; if(!pd) return; hideEdPopups(); edAddTrans(pd.from,pd.to,edParseSyms($('edSym').value)); edRender(); }
$('edPopOk').addEventListener('click',confirmSymPopup);
$('edSym').addEventListener('keydown',e=>{ if(e.key==='Enter'){ e.preventDefault(); confirmSymPopup(); } });
$('edPopCancel').addEventListener('click',()=>{ hideEdPopups(); edRender(); });
document.querySelectorAll('.chips button').forEach(b=>b.addEventListener('click',()=>{
  const inp=$('edSym'), s=b.dataset.sym;
  if (s==='ε') inp.value='ε';
  else { const cur=tokens(inp.value).filter(x=>x!=='ε'); cur.push(s); inp.value=cur.join(','); }
  inp.focus();
}));
document.addEventListener('pointerdown',e=>{ if(!$('edMenu').hidden&&!e.target.closest('#edMenu')) $('edMenu').hidden=true; },true);
$('edAddBtn').addEventListener('click',()=>{
  const f=+$('edFrom').value, t=+$('edTo').value; if(!stById(f)||!stById(t)) return;
  edAddTrans(f,t,edParseSyms($('edAddSym').value)); $('edAddSym').value=''; edRender();
});
$('edAddSym').addEventListener('keydown',e=>{ if(e.key==='Enter') $('edAddBtn').click(); });
document.addEventListener('keydown',e=>{
  if ($('editor').hidden) return;
  const typing=/^(INPUT|TEXTAREA|SELECT)$/.test(e.target.tagName);
  if (e.key==='Escape') {
    if (!$('edPop').hidden||!$('edMenu').hidden||ED.linkFrom!=null) { hideEdPopups(); ED.linkFrom=null; edRender(); }
    
    return;
  }
  if (typing) return;
  if ((e.key==='Delete'||e.key==='Backspace')&&ED.sel) { e.preventDefault(); ED.sel.type==='state'?edDeleteState(ED.sel.id):edDeleteEdge(ED.sel.from,ED.sel.to); }
  else if (/^[1-4]$/.test(e.key)) setTool(['select','state','trans','delete'][+e.key-1]);
});
/* ---------- Pestañas Editor / Conversión (como las ventanas de JFLAP) ---------- */
function markTabs(editorActive){
  $('tabEditor').setAttribute('aria-selected',String(editorActive));
  $('tabResults').setAttribute('aria-selected',String(!editorActive));
}
function openEditor(){ $('results').hidden=true; $('editor').hidden=false; markTabs(true); setTool(ED.states.length?'trans':'state'); }
function closeEditor(){ hideEdPopups(); ED.linkFrom=null; $('editor').hidden=true; $('results').hidden=false; markTabs(false); }
$('tabEditor').addEventListener('click',openEditor);
$('miEditor').addEventListener('click',openEditor);
$('tabResults').addEventListener('click',closeEditor);
$('miResults').addEventListener('click',closeEditor);
$('edClose').addEventListener('click',closeEditor);
$('edClear').addEventListener('click',()=>{ Object.assign(ED,{states:[],trans:new Map(),finals:new Set(),start:null,sel:null,nextId:0,linkFrom:null}); openEditor(); setTool('state'); });
$('edToDfa').addEventListener('click',()=>{ const p=edToStruct(); closeEditor(); showConversion('toDfa',p,'Tu autómata'); });
$('edToNfa').addEventListener('click',()=>{ const p=edToStruct(); if(!analyze(p).det) return; closeEditor(); showConversion('toNfa',p,'Tu autómata'); });
addEventListener('resize',()=>{ if(!$('editor').hidden) edRender(); });

function loadExample(k){ const e=EXAMPLES[k], p=parseText(e.trans,e.start,e.finals); edLoadStruct(p); showConversion(e.dir,p,`Ejemplo: ${e.name}`); }

/* ---------- Barra de menús ---------- */
const menus=[...document.querySelectorAll('.menu')];
const closeMenus=()=>menus.forEach(m=>m.classList.remove('open'));
menus.forEach(m=>{
  const title=m.querySelector('.mtitle');
  title.addEventListener('click',e=>{ e.stopPropagation(); const was=m.classList.contains('open'); closeMenus(); if(!was) m.classList.add('open'); });
  title.addEventListener('mouseenter',()=>{ if(menus.some(x=>x.classList.contains('open'))){ closeMenus(); m.classList.add('open'); } });
});
document.addEventListener('click',closeMenus);
document.querySelectorAll('[data-ex]').forEach(b=>b.addEventListener('click',()=>{ loadExample(b.dataset.ex); openEditor(); }));
$('miHelp').addEventListener('click',()=>{ openEditor(); $('edHelp').open=true; });

loadExample('ends01');
openEditor();
