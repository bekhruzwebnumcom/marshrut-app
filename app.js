// app.js — интерфейс, карта, хранение, Telegram, запросы к OSRM и Nominatim.
// Маршрут считает planner.js; сюда — только подготовка данных и показ результата.
import {ll,haversine,estimateMatrix,buildPlan,zoneNodes,rerouteDay,movePoint,replanDays} from './planner.js?v=5';

const tg=window.Telegram&&window.Telegram.WebApp;
const inTg=!!(tg&&tg.initData);
const ver=v=>!!(tg&&tg.isVersionAtLeast&&tg.isVersionAtLeast(v));
if(tg){try{tg.ready();tg.expand();if(ver('7.7'))tg.disableVerticalSwipes();}catch(e){}}
const $=s=>document.querySelector(s);
const esc=s=>String(s==null?'':s).replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));

/* ---------- Telegram: тема и главная кнопка ---------- */
const root=document.documentElement;
// Цвета приходят из темы Telegram (переменные --tg-theme-*); класс .dark — для карты и запасных цветов
function applyTheme(){
  const dark=inTg?tg.colorScheme==='dark':!!(window.matchMedia&&matchMedia('(prefers-color-scheme: dark)').matches);
  root.classList.toggle('dark',dark);
  if(!inTg)return;
  try{if(ver('6.1')){tg.setHeaderColor('bg_color');tg.setBackgroundColor('bg_color');}if(ver('7.10'))tg.setBottomBarColor('bg_color');}catch(e){}
}
applyTheme();
if(inTg)tg.onEvent('themeChanged',applyTheme);
else if(window.matchMedia)matchMedia('(prefers-color-scheme: dark)').addEventListener('change',applyTheme);
// Главная кнопка Telegram повторяет кнопку страницы с атрибутом data-main; саму кнопку страницы в Telegram прячем
const MB=inTg&&ver('6.0')?tg.MainButton:null;let mainEl=null;
if(MB){root.classList.add('tg-main');MB.onClick(()=>{if(mainEl&&!mainEl.disabled&&mainEl.isConnected)mainEl.click();});}
function syncMain(){
  if(!MB)return;
  const el=$('#modal').className==='show'?$('#sheet [data-main]'):tab==='route'?$('#r-build'):null;
  mainEl=el;
  try{
    if(!el){MB.hideProgress();MB.hide();return;}
    MB.setText(el.textContent.trim());
    if(el.disabled){MB.showProgress(false);MB.disable();}else{MB.hideProgress();MB.enable();}
    MB.show();
  }catch(e){}
}
const COLORS=["#e4572e","#2e86ab","#2f9e5b","#e09f1f","#8e5cd9","#d63a86","#139a9a","#6f7f1a","#c2410c","#4361ee","#9c4f2e","#5a6b7d"];
const col=i=>COLORS[i%COLORS.length];
const REGIONS=[["Ташкент",41.311,69.279],["Ташкентская область",41.05,69.75],["Андижанская область",40.783,72.344],["Бухарская область",39.767,64.423],["Джизакская область",40.116,67.842],["Кашкадарьинская область",38.861,65.789],["Навоийская область",40.084,65.379],["Наманганская область",40.998,71.672],["Самаркандская область",39.654,66.976],["Сурхандарьинская область",37.224,67.278],["Сырдарьинская область",40.49,68.784],["Ферганская область",40.384,71.784],["Хорезмская область",41.55,60.633],["Каракалпакстан",42.46,59.603]];
const LSK='rp_v1',OSRM='https://router.project-osrm.org';
let pts=[],me=null,plan=null,focusDay=null,addMode=false,tab='map',meMk=null;
const F={q:'',r:'',d:'',s:'todo',near:false,km:10};
const C={start:'',t0:'09:00',mode:'base',hours:9,width:10,max:0,stop:20,loop:false};

/* ---------- utils ---------- */
const hm=m=>{m=Math.round(m);const h=Math.floor(m/60),x=m%60;return h?h+' ч'+(x?' '+x+' мин':''):x+' мин';};
const clock=(t0,m)=>{const p=(t0||'09:00').split(':').map(Number);const x=((p[0]*60+p[1]+Math.round(m))%1440+1440)%1440;return String(Math.floor(x/60)).padStart(2,'0')+':'+String(x%60).padStart(2,'0');};
const fkm=k=>k<10?k.toFixed(1).replace('.',','):String(Math.round(k));
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const uid=()=>Date.now().toString(36)+Math.random().toString(36).slice(2,6);
const COORD=/(-?\d{1,3}\.\d+)\s*[,;\s]\s*(-?\d{1,3}\.\d+)/;
function parseLL(s){s=String(s||'').replace(/%2C/gi,',');const m=s.match(COORD);if(!m)return null;let a=+m[1],b=+m[2];if(a>50&&b<50)[a,b]=[b,a];if(Math.abs(a)>90||Math.abs(b)>180)return null;return [a,b];}
function haptic(t){try{tg&&ver('6.1')&&tg.HapticFeedback.impactOccurred(t||'light');}catch(e){}}
let tt=null;function toast(m){const t=$('#toast');t.textContent=m;t.className='show';clearTimeout(tt);tt=setTimeout(()=>t.className='',2600);}
function openLink(u){try{if(tg&&inTg)tg.openLink(u);else window.open(u,'_blank');}catch(e){window.open(u,'_blank');}}
function nearestRegion(p){let b=REGIONS[0],bd=1e9;REGIONS.forEach(r=>{const d=haversine(ll(p),[r[1],r[2]]);if(d<bd){bd=d;b=r;}});return b[0];}

/* ---------- storage: Telegram CloudStorage + localStorage ---------- */
const cs=inTg&&ver('6.9')?tg.CloudStorage:null;
const csCall=(fn,...a)=>new Promise(res=>{try{cs[fn](...a,(err,val)=>res(err?null:val));}catch(e){res(null);}});
let csChain=Promise.resolve();const csQ=(...a)=>{if(cs)csChain=csChain.then(()=>csCall(...a));};
function clean(p){return{id:String(p.id),n:String(p.n||'Точка').slice(0,120),la:+p.la,lo:+p.lo,ph:String(p.ph||'').slice(0,40),nt:String(p.nt||'').slice(0,500),r:String(p.r||''),d:String(p.d||''),c:String(p.c||''),v:p.v?1:0,g:p.g?1:0};}
const valid=p=>p&&isFinite(p.la)&&isFinite(p.lo)&&p.id!=null;
function lsSave(){try{localStorage.setItem(LSK,JSON.stringify({pts,cfg:C}));}catch(e){}}
function putPoint(p){lsSave();csQ('setItem','p_'+p.id,JSON.stringify(p));}
function dropPoint(id){lsSave();csQ('removeItem','p_'+id);}
function putCfg(){lsSave();csQ('setItem','cfg',JSON.stringify(C));}
async function loadAll(){
  let list=null,cfg=null;
  if(cs){const keys=await csCall('getKeys');if(Array.isArray(keys)){list=[];const pk=keys.filter(k=>k.startsWith('p_'));
    for(let i=0;i<pk.length;i+=50){const v=await csCall('getItems',pk.slice(i,i+50));if(v)for(const k in v){try{list.push(JSON.parse(v[k]));}catch(e){}}}
    if(keys.includes('cfg')){try{cfg=JSON.parse(await csCall('getItem','cfg'));}catch(e){}}}}
  if(!list||(!list.length&&!cs)){try{const d=JSON.parse(localStorage.getItem(LSK)||'null');if(d&&Array.isArray(d.pts)){list=d.pts;cfg=d.cfg;}}catch(e){}}
  pts=(list||[]).filter(valid).map(clean);
  if(cfg&&typeof cfg==='object')for(const k in C)if(cfg[k]!=null)C[k]=typeof C[k]==='number'?+cfg[k]:typeof C[k]==='boolean'?!!cfg[k]:String(cfg[k]);
}

/* ---------- reverse geocoding (область / район) ---------- */
const geoQ=[];let geoBusy=false;
function geocode(p){geoQ.push(p);runGeo();}
async function runGeo(){
  if(geoBusy)return;geoBusy=true;
  while(geoQ.length){const p=geoQ.shift();if(!pts.includes(p))continue;
    try{const r=await fetch(`https://nominatim.openstreetmap.org/reverse?format=jsonv2&zoom=12&accept-language=ru&lat=${p.la}&lon=${p.lo}`);const j=await r.json();const a=j.address||{};
      p.r=a.state||a.region||(a.city==='Ташкент'?'Ташкент':'')||nearestRegion(p);p.d=a.county||a.district||a.city_district||a.city||a.town||a.municipality||'';p.c=a.city||a.town||a.village||a.hamlet||p.d;p.g=1;}
    catch(e){if(!p.r)p.r=nearestRegion(p);}
    putPoint(p);renderSoon();await sleep(1100);}
  geoBusy=false;
}

/* ---------- filters ---------- */
function filtered(){
  const q=F.q.trim().toLowerCase();
  return pts.filter(p=>(!q||(p.n+' '+p.ph+' '+p.c+' '+p.d).toLowerCase().includes(q))&&(!F.r||p.r===F.r)&&(!F.d||p.d===F.d)&&(F.s==='all'||(F.s==='todo'?!p.v:p.v))&&(!F.near||!me||haversine(me,ll(p))<=F.km));
}

/* ---------- map ---------- */
const map=L.map('map',{zoomControl:false}).setView([41.4,64.6],6);
L.tileLayer('https://tile.openstreetmap.org/{z}/{x}/{y}.png',{maxZoom:19,attribution:'© OpenStreetMap'}).addTo(map);
const layerRoute=L.layerGroup().addTo(map),layerPts=L.layerGroup().addTo(map);
function fit(list){if(!list.length)return;if(list.length===1)map.setView(list[0],15);else map.fitBounds(L.latLngBounds(list),{padding:[50,50],maxZoom:15});}
function planIndex(){const m=new Map();if(plan)plan.days.forEach((d,i)=>d.pts.forEach((p,j)=>m.set(p.id,{day:i,ord:j+1})));return m;}
function renderMap(){
  layerPts.clearLayers();layerRoute.clearLayers();
  const idx=planIndex(),show=new Map(filtered().map(p=>[p.id,p]));
  if(plan){plan.days.forEach(d=>d.pts.forEach(p=>{if(pts.includes(p))show.set(p.id,p);}));
    plan.days.forEach((d,i)=>{const dim=focusDay!=null&&focusDay!==i;const line=d.geom||dayC(d);
      L.polyline(line,{color:col(i),weight:dim?3:5,opacity:dim?.18:.85,dashArray:d.geom?null:'6 8'}).addTo(layerRoute);});
    if(plan.start)L.marker(plan.start,{icon:L.divIcon({className:'',html:'<div class="start">С</div>',iconSize:[24,24]}),zIndexOffset:900}).addTo(layerRoute);}
  show.forEach(p=>{const info=idx.get(p.id),dim=focusDay!=null&&(!info||info.day!==focusDay);
    const bg=p.v?'#9aa0a6':info?col(info.day):'var(--btn)',lbl=info&&!p.v?info.ord:'';
    L.marker(ll(p),{icon:L.divIcon({className:'',html:`<div class="mk${lbl?'':' sm'}${dim?' dim':''}" style="background:${bg}">${lbl}</div>`,iconSize:lbl?[28,28]:[16,16]}),zIndexOffset:dim?0:500})
      .on('click',()=>openEdit(p.id)).addTo(layerPts);});
  $('#empty').className='empty'+(pts.length?'':' show');
  renderTop();
}
function renderTop(){
  const n=filtered().length,fs=[F.r,F.d,F.q&&('«'+F.q+'»'),F.near&&('≤'+F.km+' км')].filter(Boolean);
  let h='';
  if(plan&&focusDay!=null){const d=plan.days[focusDay];h=`<button class="chip" id="t-prev">‹</button><button class="chip pri" id="t-day">День ${focusDay+1} из ${plan.days.length} · ${d.pts.length} точ.</button><button class="chip" id="t-next">›</button><button class="chip" id="t-all">Все дни</button>`;}
  else h=`<button class="chip" id="t-f">${fs.length?esc(fs.join(' · '))+' · ':''}${n} из ${pts.length} точек</button>`+(plan?`<button class="chip pri" id="t-plan">${plan.days.length} дн. маршрута</button>`:'');
  $('#top').innerHTML=h;
  const on=(id,f)=>{const e=$(id);if(e)e.onclick=f;};
  on('#t-f',()=>setTab('points'));on('#t-plan',()=>setTab('route'));on('#t-day',()=>setTab('route'));
  on('#t-all',()=>{focusDay=null;renderMap();fit(plan.days.flatMap(d=>d.pts.map(ll)));});
  on('#t-prev',()=>showDay((focusDay-1+plan.days.length)%plan.days.length));
  on('#t-next',()=>showDay((focusDay+1)%plan.days.length));
}
function showDay(i){focusDay=i;setTab('map');renderMap();const d=plan.days[i];fit([d.from,...d.pts.map(ll)]);}
map.on('click',e=>{if(!addMode)return;setAdd(false);newPoint([+e.latlng.lat.toFixed(6),+e.latlng.lng.toFixed(6)]);});
function setAdd(on){addMode=on;$('#banner').className='banner'+(on?' show':'');$('#fab').style.display=on?'none':'grid';}

/* ---------- location ---------- */
function browserGeo(){return new Promise(res=>{if(!navigator.geolocation)return res(null);navigator.geolocation.getCurrentPosition(p=>res([p.coords.latitude,p.coords.longitude]),()=>res(null),{enableHighAccuracy:true,timeout:15000,maximumAge:30000});});}
function getLoc(){return new Promise(res=>{
  const LM=tg&&inTg&&ver('8.0')?tg.LocationManager:null;
  if(!LM)return browserGeo().then(res);
  const go=()=>{if(!LM.isLocationAvailable)return browserGeo().then(res);
    LM.getLocation(d=>{if(d&&d.latitude!=null)res([d.latitude,d.longitude]);else{toast('Нет доступа к геолокации — разрешите в настройках');try{LM.openSettings();}catch(e){}res(null);}});};
  LM.isInited?go():LM.init(go);
});}
async function locateMe(){toast('Определяю местоположение…');const c=await getLoc();if(!c){toast('Не удалось определить местоположение');return null;}
  me=c;if(meMk)meMk.setLatLng(c);else meMk=L.marker(c,{icon:L.divIcon({className:'',html:'<div class="me"></div>',iconSize:[18,18]}),zIndexOffset:1000}).addTo(map);return c;}

/* ---------- modal ---------- */
function openModal(html){$('#sheet').innerHTML=html;$('#modal').className='show';syncBack();}
function closeModal(){$('#modal').className='';syncBack();}
$('#modal').addEventListener('click',e=>{if(e.target.id==='modal')closeModal();});

function pointForm(p,isNew){
  return `<h2>${isNew?'Новая точка':'Точка'}</h2>
  <label>Название<input id="m-n" value="${esc(p.n)}"></label>
  <div class="g2" style="margin-top:8px"><label>Телефон<input id="m-ph" type="tel" value="${esc(p.ph)}"></label><label>Координаты<input id="m-ll" value="${p.la}, ${p.lo}"></label></div>
  <label style="margin-top:8px">Заметка<input id="m-nt" value="${esc(p.nt)}"></label>
  <p class="muted">${p.r?esc(p.r)+(p.d?' · '+esc(p.d):''):isNew?'Область и район определятся автоматически':'Определяю область и район…'}${me?' · '+fkm(haversine(me,ll(p)))+' км от вас':''}</p>`;
}
function readForm(p){p.n=$('#m-n').value.trim()||'Точка';p.ph=$('#m-ph').value.trim();p.nt=$('#m-nt').value.trim();const c=parseLL($('#m-ll').value);if(c&&(c[0]!==p.la||c[1]!==p.lo)){p.la=c[0];p.lo=c[1];p.g=0;p.r='';p.d='';p.c='';plan=null;return true;}return false;}
function newPoint(c,name){
  const p={id:uid(),n:name||'Точка '+(pts.length+1),la:c[0],lo:c[1],ph:'',nt:'',r:'',d:'',c:'',v:0,g:0};
  openModal(pointForm(p,true)+`<div class="row"><button class="btn pri" id="m-save">Сохранить</button><button class="btn" id="m-x">Отмена</button></div>`);
  $('#m-save').onclick=()=>{readForm(p);pts.push(p);plan=null;putPoint(p);geocode(p);closeModal();haptic('medium');toast('Точка добавлена');renderAll();};
  $('#m-x').onclick=closeModal;
  setTimeout(()=>{const i=$('#m-n');i.focus();i.select();},50);
}
function openEdit(id){
  const p=pts.find(x=>x.id===id);if(!p)return;const info=planIndex().get(id);
  const canMove=info&&plan.days.length>1;
  openModal(pointForm(p,false)+(info?`<p class="muted" style="margin-top:-6px">В маршруте: день ${info.day+1}, точка №${info.ord}</p>`:'')+
  (canMove?`<div class="row" style="align-items:flex-end;margin-top:0"><label style="flex:1">Перенести в день<select id="m-day">${plan.days.map((d,k)=>`<option value="${k}"${k===info.day?' selected':''}>День ${k+1} · ${esc(d.name)} (${d.pts.length})</option>`).join('')}</select></label><button class="btn" id="m-move">Перенести</button></div>`:'')+
  `<div class="row"><button class="btn pri" id="m-save">Сохранить</button><button class="btn" id="m-v">${p.v?'Вернуть в план':'Посещено'}</button><button class="btn" id="m-go">Яндекс Карты</button>${p.ph?'<button class="btn" id="m-call">Написать в Telegram</button>':''}<button class="btn danger" id="m-del">Удалить</button></div>`);
  $('#m-save').onclick=()=>{if(readForm(p))geocode(p);putPoint(p);closeModal();renderAll();};
  $('#m-v').onclick=()=>{p.v=p.v?0:1;putPoint(p);closeModal();haptic();renderAll();};
  $('#m-go').onclick=()=>openLink(`https://yandex.ru/maps/?rtext=~${p.la},${p.lo}&rtt=auto`);
  if(canMove)$('#m-move').onclick=()=>{const t=+$('#m-day').value;if(t===info.day){toast('Точка уже в этом дне');return;}closeModal();movePointTo(p,t);};
  if(p.ph)$('#m-call').onclick=()=>{const n=p.ph.replace(/[^\d+]/g,'');openLink('https://t.me/+'+n.replace(/^\+/,''));};
  $('#m-del').onclick=()=>{const del=()=>{pts=pts.filter(x=>x!==p);plan=null;dropPoint(p.id);closeModal();renderAll();toast('Точка удалена');};
    if(tg&&inTg&&ver('6.2'))tg.showConfirm('Удалить «'+p.n+'»?',ok=>{if(ok)del();});else del();};
}
function addMenu(){
  openModal(`<h2>Добавить точку</h2><div style="display:grid;gap:8px">
    <button class="btn pri wide" id="a-gps">Моё местоположение (я на месте)</button>
    <button class="btn wide" id="a-map">Указать на карте</button>
    <button class="btn wide" id="a-imp">Вставить ссылку или список</button></div>`);
  $('#a-gps').onclick=async()=>{closeModal();const c=await locateMe();if(c){map.setView(c,16);newPoint(c);}};
  $('#a-map').onclick=()=>{closeModal();setTab('map');setAdd(true);};
  $('#a-imp').onclick=importModal;
}
function importModal(){
  openModal(`<h2>Импорт точек</h2><textarea id="i-t" placeholder="Аптека №5; 40.0912, 65.3801&#10;Магазин Баракат +998 90 123 45 67 https://yandex.uz/maps/?ll=65.36%2C40.13&#10;https://maps.google.com/?q=40.56,65.69"></textarea>
   <p class="muted">Каждая строка — одна точка: название, телефон (необязательно) и координаты или ссылка из Яндекс/Google Карт. Можно скопировать столбцы из Excel. Короткие ссылки вида yandex.uz/maps/-/… не содержат координат — откройте их и скопируйте полную ссылку.</p>
   <div class="row"><button class="btn pri" id="i-go">Добавить</button><button class="btn" id="i-x">Отмена</button></div>`);
  $('#i-x').onclick=closeModal;
  $('#i-go').onclick=()=>{
    const lines=$('#i-t').value.split(/\n+/).map(s=>s.trim()).filter(Boolean),add=[];let bad=0;
    lines.forEach(l=>{const c=parseLL(l);if(!c){bad++;return;}
      const phm=l.match(/\+?998[\s\-()]*\d{2}[\s\-()]*\d{3}[\s\-]*\d{2}[\s\-]*\d{2}/);
      let n=l.replace(/https?:\/\/\S+/g,'').replace(COORD,'').replace(phm?phm[0]:'\u0000','').replace(/[;|\t]+/g,' ').replace(/\s+/g,' ').trim().replace(/[,\s-]+$/,'');
      add.push({id:uid(),n:n||'Точка '+(pts.length+add.length+1),la:c[0],lo:c[1],ph:phm?phm[0].trim():'',nt:'',r:'',d:'',c:'',v:0,g:0});});
    add.forEach(p=>{pts.push(p);putPoint(p);geocode(p);});
    if(add.length)plan=null;closeModal();renderAll();
    toast(`Добавлено: ${add.length}`+(bad?` · не распознано: ${bad}`:''));
    if(add.length){setTab('map');fit(add.map(ll));}
  };
}

/* ---------- route building ---------- */
function zoneName(z){const c={};z.forEach(p=>{const k=p.c||p.d||p.r||nearestRegion(p);c[k]=(c[k]||0)+1;});return Object.entries(c).sort((a,b)=>b[1]-a[1])[0][0];}
async function osrmTable(nodes){
  if(nodes.length<2||nodes.length>100)return null;
  const ctl=new AbortController(),to=setTimeout(()=>ctl.abort(),15000);
  try{const r=await fetch(`${OSRM}/table/v1/driving/${nodes.map(c=>c[1].toFixed(6)+','+c[0].toFixed(6)).join(';')}?annotations=duration,distance`,{signal:ctl.signal});
    const j=await r.json();if(j.code!=='Ok'||!j.durations)return null;
    const e=estimateMatrix(nodes);
    return{km:j.distances.map((row,i)=>row.map((v,k)=>v==null?e.km[i][k]:v/1000)),min:j.durations.map((row,i)=>row.map((v,k)=>v==null?e.min[i][k]:v/60)),est:false};
  }catch(e){return null;}finally{clearTimeout(to);}
}
async function build(){
  readCfg();
  const list=filtered().filter(p=>!p.v);
  if(!list.length){toast('Нет непосещённых точек по фильтру');return;}
  const btn=$('#r-build');btn.disabled=true;btn.textContent='Считаю маршрут…';syncMain();haptic();
  try{
    const getMatrix=async nodes=>(await osrmTable(nodes))||estimateMatrix(nodes);
    const pl=await buildPlan(list,C,parseLL(C.start),getMatrix);
    pl.days.forEach(d=>d.name=zoneName(d.pts));
    plan=pl;focusDay=null;
    renderRoute();renderMap();toast(`Готово: ${plan.days.length} дн.`);haptic('medium');
    loadGeoms(plan);
  }finally{btn.disabled=false;btn.textContent='Построить маршрут';syncMain();}
}
/* ручная правка: точка — в другой день, затронутые дни пересчитываются по дорогам */
let moving=false;
async function movePointTo(p,t){
  if(!plan||moving)return;
  const pl=plan,m=movePoint(pl,p,t);if(!m.changed.length)return;
  moving=true;toast('Переношу точку…');
  try{
    const getMatrix=async nodes=>(await osrmTable(nodes))||estimateMatrix(nodes);
    const r=await replanDays(m.plan,m.changed,C,getMatrix);
    if(plan!==pl)return;
    r.touched.forEach(i=>{r.plan.days[i].name=zoneName(r.plan.days[i].pts);});
    plan=r.plan;
    const ni=plan.days.findIndex(d=>d.pts.includes(p));if(focusDay!=null)focusDay=ni;
    renderRoute();renderMap();haptic('medium');toast(`Точка перенесена в день ${ni+1}`);
    loadGeoms(plan,r.touched.map(i=>plan.days[i]));
  }finally{moving=false;}
}
async function loadGeoms(pl,list=pl.days){
  for(const d of list){if(plan!==pl)return;const c=dayC(d);if(c.length<2||c.length>90)continue;
    try{const r=await fetch(`${OSRM}/route/v1/driving/${c.map(x=>x[1].toFixed(6)+','+x[0].toFixed(6)).join(';')}?overview=full&geometries=geojson`);const j=await r.json();
      if(j.code==='Ok'&&j.routes[0]){d.geom=j.routes[0].geometry.coordinates.map(x=>[x[1],x[0]]);if(plan===pl)renderMap();}}catch(e){}
    await sleep(300);}
}
const dayC=d=>{const c=[d.from,...d.pts.slice(d.skip||0).map(ll)];if(d.ret&&plan&&plan.start)c.push(plan.start);return c;};
const chunks=c=>{const o=[];for(let k=0;k<c.length-1;k+=9)o.push(c.slice(k,k+10));return o;};
const yan=c=>'https://yandex.ru/maps/?rtext='+c.map(x=>x[0].toFixed(6)+','+x[1].toFixed(6)).join('~')+'&rtt=auto';
const goo=c=>'https://www.google.com/maps/dir/'+c.map(x=>x[0].toFixed(6)+','+x[1].toFixed(6)).join('/');
function shareDay(i){
  const d=plan.days[i],c=dayC(d);
  const text=`Маршрут, день ${i+1}: ${d.pts.length} точек, ~${Math.round(d.km)} км\n`+d.pts.map((p,k)=>`${k+1}. ${p.n}${p.ph?' '+p.ph:''}`).join('\n');
  const u='https://t.me/share/url?url='+encodeURIComponent(yan(c.slice(0,10)))+'&text='+encodeURIComponent(text);
  try{if(tg&&inTg&&ver('6.1'))tg.openTelegramLink(u);else window.open(u,'_blank');}catch(e){window.open(u,'_blank');}
}
function renderRoute(){
  const el=$('#days');
  if(!plan){el.innerHTML='';return;}
  const {days}=plan,km=days.reduce((a,d)=>a+d.km,0),n=days.reduce((a,d)=>a+d.pts.length,0);
  el.innerHTML=`<div class="card"><h3>${days.length} дн. · ${n} точек · ~${Math.round(km)} км</h3><p class="muted" style="margin:4px 0 0">${plan.real?'Расстояния и время — по реальным дорогам.':plan.partial?'Часть дней посчитана по дорогам, часть — оценочно (нет связи с сервером маршрутов).':'Сервер маршрутов недоступен — расстояния оценочные (прямая × 1,3).'}</p></div>`+
  days.map((d,i)=>{const gl=chunks(dayC(d)),vis=d.pts.filter(p=>p.v).length;
    const info=d.skip!=null
      ?`${vis}/${d.pts.length} точек · пересчитано от вашего места: ещё ~${Math.round(d.km)} км · в пути ${hm(d.drive)} · финиш ~${clock('00:00',d.at+d.drive+d.stopM)}`
      :`${vis?vis+'/':''}${d.pts.length} точек · ~${Math.round(d.km)} км${d.ret?' (с возвратом)':''} · в пути ${hm(d.drive)} · финиш ~${clock(C.t0,d.drive+d.stopM)}`;
    return `<div class="day"><div class="dh"><span class="num" style="background:${col(i)}">${i+1}</span><div><h3>День ${i+1} · ${esc(d.name)}</h3>
    <p class="muted" style="margin:2px 0 0">${info}${d.drive+d.stopM>C.hours*60?` · <b style="color:var(--danger)">⚠ дольше ${C.hours} ч</b>`:''}</p></div></div>
    <div class="row"><button class="btn sm pri" data-guide="${i}">Начать объезд</button><button class="btn sm" data-show="${i}">На карте</button>${gl.map((g,k)=>`<button class="btn sm" data-yan="${i}:${k}">Яндекс${gl.length>1?' '+(k+1):''}</button>`).join('')}${gl.map((g,k)=>`<button class="btn sm" data-goo="${i}:${k}">Google${gl.length>1?' '+(k+1):''}</button>`).join('')}<button class="btn sm" data-share="${i}">Отправить</button></div>
    <details><summary>Порядок объезда</summary><ol>${d.pts.map(p=>`<li data-pid="${esc(p.id)}"${p.v?' style="text-decoration:line-through;opacity:.6"':''}>${esc(p.n)}</li>`).join('')}</ol></details></div>`;}).join('');
}
$('#days').addEventListener('click',e=>{
  const t=e.target.closest('[data-guide],[data-show],[data-yan],[data-goo],[data-share],[data-pid]');if(!t||!plan)return;
  if(t.dataset.guide!=null)guide(+t.dataset.guide);
  else if(t.dataset.show!=null)showDay(+t.dataset.show);
  else if(t.dataset.yan!=null){const [i,k]=t.dataset.yan.split(':').map(Number);openLink(yan(chunks(dayC(plan.days[i]))[k]));}
  else if(t.dataset.goo!=null){const [i,k]=t.dataset.goo.split(':').map(Number);openLink(goo(chunks(dayC(plan.days[i]))[k]));}
  else if(t.dataset.share!=null)shareDay(+t.dataset.share);
  else if(t.dataset.pid)openEdit(t.dataset.pid);
});


/* ---------- объезд по очереди ---------- */
function guide(i){
  if(!plan||!plan.days[i])return;const d=plan.days[i];focusDay=i;
  const next=d.pts.find(p=>!p.v&&pts.includes(p));renderMap();
  if(!next){openModal(`<h2>День ${i+1} завершён</h2><p class="muted">Все точки дня отмечены.</p><div class="row">${d.ret?'<button class="btn pri" id="g-home">Вернуться на старт</button>':''}${i+1<plan.days.length?`<button class="btn${d.ret?'':' pri'}" id="g-nd">Начать день ${i+2}</button>`:''}<button class="btn" id="g-x">Закрыть</button></div>`);
    if(d.ret)$('#g-home').onclick=()=>openLink(`https://yandex.ru/maps/?rtext=~${plan.start[0]},${plan.start[1]}&rtt=auto`);
    if(i+1<plan.days.length)$('#g-nd').onclick=()=>guide(i+1);$('#g-x').onclick=closeModal;renderRoute();return;}
  const k=d.pts.indexOf(next),done=d.pts.filter(p=>p.v).length;map.setView(ll(next),Math.max(map.getZoom(),14));
  openModal(`<p class="muted" style="margin:0">День ${i+1} · точка ${k+1} из ${d.pts.length} · отмечено ${done}</p><h2 style="margin-top:4px">${esc(next.n)}</h2>
   <p class="muted">${esc([next.d||next.r,next.ph,next.nt].filter(Boolean).join(' · '))}${me?' · '+fkm(haversine(me,ll(next)))+' км по прямой':''}</p>
   <div style="display:grid;gap:8px"><button class="btn pri wide" id="g-go">Поехать — Яндекс Карты</button><button class="btn wide" id="g-done" data-main>Посещено → следующая</button>
   <button class="btn wide" id="g-re">Пересчитать остаток от моего места</button>
   <div class="g2"><button class="btn" id="g-skip">Пропустить (в конец)</button><button class="btn" id="g-x">Закрыть</button></div></div>`);
  $('#g-go').onclick=()=>openLink(`https://yandex.ru/maps/?rtext=~${next.la},${next.lo}&rtt=auto`);
  $('#g-done').onclick=()=>{next.v=1;putPoint(next);haptic('medium');guide(i);};
  $('#g-re').onclick=()=>reroute(i);
  $('#g-skip').onclick=()=>{d.pts.splice(k,1);d.pts.push(next);guide(i);};
  $('#g-x').onclick=()=>{closeModal();renderRoute();};
}
/* «Пересчитать остаток»: оставшиеся точки дня — заново по порядку от текущего GPS */
async function reroute(i){
  const pl=plan,d=pl&&pl.days[i];if(!d)return;
  const here=await locateMe();if(!here||plan!==pl)return;
  const rest=d.pts.filter(p=>!p.v&&pts.includes(p));if(!rest.length)return guide(i);
  const back=d.ret?pl.start:null,nodes=zoneNodes(here,rest,back);
  toast('Пересчитываю остаток…');
  const M=(await osrmTable(nodes))||estimateMatrix(nodes);if(plan!==pl)return;
  const nd=rerouteDay(d,rest,here,M,!!back,C.stop),now=new Date();
  nd.name=d.name;nd.at=now.getHours()*60+now.getMinutes();pl.days[i]=nd;
  haptic('medium');toast(M.est?'Порядок пересчитан (оценочно)':'Порядок пересчитан');
  guide(i);loadGeoms(pl,[nd]);
}
/* ---------- points list ---------- */
function renderFilters(){
  const regs=[...new Set(pts.map(p=>p.r).filter(Boolean))].sort((a,b)=>a.localeCompare(b,'ru'));
  if(F.r&&!regs.includes(F.r))F.r='';
  $('#f-r').innerHTML='<option value="">Все области</option>'+regs.map(r=>`<option${r===F.r?' selected':''}>${esc(r)}</option>`).join('');
  const ds=[...new Set(pts.filter(p=>!F.r||p.r===F.r).map(p=>p.d).filter(Boolean))].sort((a,b)=>a.localeCompare(b,'ru'));
  if(F.d&&!ds.includes(F.d))F.d='';
  $('#f-d').innerHTML='<option value="">Все</option>'+ds.map(d=>`<option${d===F.d?' selected':''}>${esc(d)}</option>`).join('');
}
function renderList(){
  renderFilters();
  let list=filtered().slice();const srt=$('#f-sort').value,idx=planIndex();
  if(srt==='route'&&plan)list.sort((a,b)=>{const x=idx.get(a.id),y=idx.get(b.id);return (x?x.day*1e4+x.ord:1e9)-(y?y.day*1e4+y.ord:1e9);});
  else if(srt==='dist'&&me)list.sort((a,b)=>haversine(me,ll(a))-haversine(me,ll(b)));
  else if(srt==='name')list.sort((a,b)=>a.n.localeCompare(b.n,'ru',{numeric:true}));
  $('#f-count').textContent=`Показано ${list.length} из ${pts.length}`+(F.near&&!me?' · местоположение не определено':'');
  $('#list').innerHTML=list.length?list.map(p=>`<div class="item${p.v?' done':''}" data-pid="${esc(p.id)}">${idx.get(p.id)?`<span class="num" style="width:26px;height:26px;font-size:12px;background:${p.v?'#9aa0a6':col(idx.get(p.id).day)}">${idx.get(p.id).ord}</span>`:'<span class="dot"></span>'}<div><div class="nm">${esc(p.n)}</div><div class="sub">${esc([p.d||p.r||(p.g?'':'определяю район…'),p.ph].filter(Boolean).join(' · '))}</div></div>${me?`<span class="km">${fkm(haversine(me,ll(p)))} км</span>`:''}</div>`).join(''):'<p class="muted">Ничего не найдено.</p>';
}
$('#list').addEventListener('click',e=>{const t=e.target.closest('[data-pid]');if(t)openEdit(t.dataset.pid);});
$('#f-q').addEventListener('input',e=>{F.q=e.target.value;renderList();renderMap();});
$('#f-r').addEventListener('change',e=>{F.r=e.target.value;F.d='';renderList();renderMap();});
$('#f-d').addEventListener('change',e=>{F.d=e.target.value;renderList();renderMap();});
$('#f-sort').addEventListener('change',async e=>{if(e.target.value==='dist'&&!me)await locateMe();renderList();});
$('#f-s').addEventListener('change',e=>{F.s=e.target.value;renderList();renderMap();});
$('#f-km').addEventListener('change',e=>{F.km=Math.max(1,+e.target.value||10);renderList();renderMap();});
$('#f-near').addEventListener('change',async e=>{F.near=e.target.checked;if(F.near&&!me)await locateMe();renderList();renderMap();});
$('#l-map').onclick=()=>{setTab('map');fit(filtered().map(ll));};
$('#l-imp').onclick=importModal;

/* ---------- settings ---------- */
const CF=[['start','#c-start'],['t0','#c-t0'],['hours','#c-hours'],['width','#c-width'],['stop','#c-stop']];
function syncMode(){$('#c-loop-row').style.display=C.mode==='stay'?'':'none';}
function fillCfg(){CF.forEach(([k,s])=>$(s).value=C[k]);$('#c-max').value=C.max||'';$('#c-mode').value=C.mode==='stay'?'stay':'base';$('#c-loop').checked=C.loop;syncMode();}
function readCfg(){C.start=$('#c-start').value.trim();C.t0=$('#c-t0').value||'09:00';C.mode=$('#c-mode').value==='stay'?'stay':'base';C.hours=Math.max(1,+$('#c-hours').value||9);C.width=Math.max(1,+$('#c-width').value||10);C.max=Math.max(0,Math.floor(+$('#c-max').value||0));C.stop=Math.max(0,+$('#c-stop').value||0);C.loop=$('#c-loop').checked;syncMode();putCfg();}
document.querySelectorAll('#p-route .card input,#p-route .card select').forEach(i=>i.addEventListener('change',readCfg));
$('#c-me').onclick=async()=>{const c=await locateMe();if(c){$('#c-start').value=c[0].toFixed(6)+', '+c[1].toFixed(6);readCfg();}};
$('#c-clr').onclick=()=>{$('#c-start').value='';readCfg();};
$('#r-build').onclick=build;

/* ---------- tabs & back button (главная кнопка Telegram синхронизируется вместе с «Назад») ---------- */
function setTab(t){tab=t;document.querySelectorAll('nav.tabs button').forEach(b=>b.classList.toggle('on',b.dataset.tab===t));
  $('#p-points').classList.toggle('on',t==='points');$('#p-route').classList.toggle('on',t==='route');
  if(t==='points')renderList();if(t==='route')renderRoute();if(t==='map')setTimeout(()=>map.invalidateSize(),50);
  if(t!=='map')setAdd(false);syncBack();}
document.querySelectorAll('nav.tabs button').forEach(b=>b.onclick=()=>{haptic();setTab(b.dataset.tab);});
function syncBack(){syncMain();if(!tg||!inTg||!ver('6.1'))return;const need=$('#modal').className==='show'||tab!=='map'||addMode;try{need?tg.BackButton.show():tg.BackButton.hide();}catch(e){}}
if(tg&&inTg&&ver('6.1'))tg.BackButton.onClick(()=>{if($('#modal').className==='show')closeModal();else if(addMode){setAdd(false);syncBack();}else setTab('map');});

/* ---------- demo data ---------- */
function demo(){
  const T=[["Навои",40.0844,65.3792,"Навоийская область","город Навои",18,.035],["Кармана",40.141,65.36,"Навоийская область","Карманинский район",5,.012],["Кызылтепа",40.032,64.851,"Навоийская область","Кызылтепинский район",5,.018],["Нурата",40.564,65.688,"Навоийская область","Нуратинский район",5,.018],["Зарафшан",41.574,64.201,"Навоийская область","город Зарафшан",5,.025],["Учкудук",42.156,63.555,"Навоийская область","Учкудукский район",4,.015]];
  const kinds=["Магазин","Аптека","Маркет","Кафе","Склад","Офис","Супермаркет","Автосервис"];let s=11;const rnd=()=>(s=(s*16807)%2147483647)/2147483647;
  T.forEach(t=>{for(let i=0;i<t[5];i++){const a=rnd()*Math.PI*2,d=Math.sqrt(rnd())*t[6];
    const p={id:uid()+i,n:kinds[Math.floor(rnd()*kinds.length)]+' · '+t[0]+' '+(i+1),la:+(t[1]+Math.sin(a)*d).toFixed(6),lo:+(t[2]+Math.cos(a)*d/Math.cos(t[1]*Math.PI/180)).toFixed(6),ph:'',nt:'Пример',r:t[3],d:t[4],c:t[0],v:0,g:1};pts.push(p);putPoint(p);}});
  plan=null;renderAll();fit(pts.map(ll));toast('Загружено 42 тестовые точки');
}
$('#e-demo').onclick=demo;

/* ---------- wiring ---------- */
$('#f-add').onclick=addMenu;
$('#f-me').onclick=async()=>{const c=await locateMe();if(c)map.setView(c,15);};
$('#b-cancel').onclick=()=>{setAdd(false);syncBack();};
let rs=null;function renderSoon(){clearTimeout(rs);rs=setTimeout(renderAll,250);}
function renderAll(){renderMap();if(tab==='points')renderList();if(tab==='route')renderRoute();}
loadAll().then(()=>{fillCfg();renderAll();if(pts.length)fit(pts.map(ll));pts.filter(p=>!p.g).forEach(geocode);});
