
"use strict";
/*═══════════════════════════════════════════════════════════════════════════════
  VALE DE AURORIA — colony simulation
  Part 1 · core: math, rng, noise, audio, dom helpers
═══════════════════════════════════════════════════════════════════════════════*/

/* ── math ─────────────────────────────────────────────────────────────── */
const PI=Math.PI, TAU=PI*2;
const clamp=(v,a,b)=>v<a?a:(v>b?b:v);
const lerp=(a,b,t)=>a+(b-a)*t;
const inv=(a,b,v)=>(v-a)/(b-a);
const sat=v=>v<0?0:(v>1?1:v);
const smooth=t=>t*t*(3-2*t);
const smoother=t=>t*t*t*(t*(t*6-15)+10);
const dist2=(ax,ay,bx,by)=>{const dx=ax-bx,dy=ay-by;return dx*dx+dy*dy;};
const dist=(ax,ay,bx,by)=>Math.hypot(ax-bx,ay-by);
const sign=Math.sign, abs=Math.abs, floor=Math.floor, ceil=Math.ceil, round=Math.round, min=Math.min, max=Math.max;
const rand=(a=1,b=0)=>b+Math.random()*(a-b);
const randInt=(a,b)=>floor(a+Math.random()*(b-a+1));
const pick=arr=>arr[(Math.random()*arr.length)|0];
const chance=p=>Math.random()<p;
const angLerp=(a,b,t)=>{let d=((b-a+PI)%TAU+TAU)%TAU-PI;return a+d*t;};
function fmt(n){n=Math.round(n);if(Math.abs(n)>=1e6)return(n/1e6).toFixed(2)+"M";if(Math.abs(n)>=1e4)return(n/1e3).toFixed(1)+"k";return String(n);}
function sgn(n){return (n>0?"+":"")+n;}

/* ── seeded rng ───────────────────────────────────────────────────────── */
function hashStr(s){let h=2166136261>>>0;for(let i=0;i<s.length;i++){h^=s.charCodeAt(i);h=Math.imul(h,16777619);}return h>>>0;}
function mulberry32(a){return function(){a|=0;a=a+0x6D2B79F5|0;let t=Math.imul(a^a>>>15,1|a);t=t+Math.imul(t^t>>>7,61|t)^t;return((t^t>>>14)>>>0)/4294967296;};}
class RNG{constructor(seed){this.r=mulberry32(typeof seed==="number"?seed:hashStr(String(seed)));this.seed=seed;}
  next(){return this.r();} float(a=0,b=1){return a+this.r()*(b-a);} int(a,b){return floor(a+this.r()*(b-a+1));}
  pick(arr){return arr[floor(this.r()*arr.length)];} chance(p){return this.r()<p;}
  shuffle(a){for(let i=a.length-1;i>0;i--){const j=floor(this.r()*(i+1));[a[i],a[j]]=[a[j],a[i]];}return a;}}

/* ── perlin / value noise ─────────────────────────────────────────────── */
class Perlin{
  constructor(seed){
    const r=mulberry32(seed>>>0); const p=new Uint8Array(256);
    for(let i=0;i<256;i++)p[i]=i;
    for(let i=255;i>0;i--){const j=(r()*(i+1))|0;const t=p[i];p[i]=p[j];p[j]=t;}
    this.perm=new Uint8Array(512); this.permMod12=new Uint8Array(512);
    for(let i=0;i<512;i++){this.perm[i]=p[i&255];this.permMod12[i]=this.perm[i]%12;}
  }
  static grad(h,x,y){switch(h&7){case 0:return x+y;case 1:return -x+y;case 2:return x-y;case 3:return -x-y;
    case 4:return x;case 5:return -x;case 6:return y;default:return -y;}}
  noise2(x,y){
    const X=Math.floor(x)&255, Y=Math.floor(y)&255;
    x-=Math.floor(x); y-=Math.floor(y);
    const u=smoother(x), v=smoother(y);
    const p=this.perm;
    const aa=p[p[X]+Y], ab=p[p[X]+Y+1], ba=p[p[X+1]+Y], bb=p[p[X+1]+Y+1];
    const g=Perlin.grad;
    const x1=lerp(g(aa,x,y),g(ba,x-1,y),u);
    const x2=lerp(g(ab,x,y-1),g(bb,x-1,y-1),u);
    return lerp(x1,x2,v)*0.7071;
  }
  fbm(x,y,oct=4,lac=2.0,gain=0.5){
    let a=1,f=1,s=0,n=0;
    for(let i=0;i<oct;i++){s+=a*this.noise2(x*f,y*f);n+=a;a*=gain;f*=lac;}
    return s/n;
  }
  ridged(x,y,oct=4){
    let a=1,f=1,s=0,n=0;
    for(let i=0;i<oct;i++){let v=1-Math.abs(this.noise2(x*f,y*f));s+=a*v*v;n+=a;a*=.5;f*=2;}
    return s/n;
  }
}

/* ── color helpers ────────────────────────────────────────────────────── */
function hex2rgb(h){h=h.replace("#","");if(h.length===3)h=h[0]+h[0]+h[1]+h[1]+h[2]+h[2];
  return [parseInt(h.slice(0,2),16),parseInt(h.slice(2,4),16),parseInt(h.slice(4,6),16)];}
function rgb2css(c,a){return a===undefined?`rgb(${c[0]|0},${c[1]|0},${c[2]|0})`:`rgba(${c[0]|0},${c[1]|0},${c[2]|0},${a})`;}
function mixRGB(a,b,t){return [lerp(a[0],b[0],t),lerp(a[1],b[1],t),lerp(a[2],b[2],t)];}
function shade(c,f){return [clamp(c[0]*f,0,255),clamp(c[1]*f,0,255),clamp(c[2]*f,0,255)];}
function tint(c,t,amt){return mixRGB(c,t,amt);}
/* cache css strings to avoid GC churn */
const _cc=new Map();
function css(c,a){
  const r=c[0]|0,g=c[1]|0,b=c[2]|0;
  if(a===undefined){const k=(r<<16)|(g<<8)|b;let s=_cc.get(k);if(!s){s=`rgb(${r},${g},${b})`;_cc.set(k,s);}return s;}
  const aa=Math.round(a*100)/100;const k=((r<<16)|(g<<8)|b)^0;const kk=k+"|"+aa;let s=_cc.get(kk);
  if(!s){s=`rgba(${r},${g},${b},${aa})`;if(_cc.size<9000)_cc.set(kk,s);}return s;
}
function hsl(h,s,l,a){return a===undefined?`hsl(${h} ${s}% ${l}%)`:`hsla(${h} ${s}% ${l}% / ${a})`;}

/* ── dom ──────────────────────────────────────────────────────────────── */
const $=s=>document.querySelector(s);
const $$=s=>Array.from(document.querySelectorAll(s));
function el(tag,cls,html){const e=document.createElement(tag);if(cls)e.className=cls;if(html!==undefined)e.innerHTML=html;return e;}
function on(t,ev,fn,o){t.addEventListener(ev,fn,o);}

/* ── svg icon library (inline, no assets) ─────────────────────────────── */
const ICONS={
  wood:'<svg viewBox="0 0 24 24"><ellipse cx="6.5" cy="12" rx="3.4" ry="6.2" fill="#c98f4e"/><ellipse cx="6.5" cy="12" rx="1.7" ry="3.3" fill="#8a5a28"/><path d="M6.5 5.8h10.2a6.2 6.2 0 010 12.4H6.5z" fill="#a06a34"/><path d="M6.5 5.8h10.2a6.2 6.2 0 010 12.4" fill="none" stroke="#6d4520" stroke-width=".8"/><path d="M11 8.6h4.4M10.4 12h6.2M11 15.4h4.4" stroke="#7d4f24" stroke-width=".9" stroke-linecap="round"/></svg>',
  stone:'<svg viewBox="0 0 24 24"><path d="M4 15.6L7.4 7.2l5.8-2.4 6 4.4-1.4 8.6-6.4 3.4z" fill="#9aa4b2"/><path d="M7.4 7.2l5.8-2.4 6 4.4-5.6 2.6z" fill="#c3ccd8"/><path d="M13.2 4.8l5.6 4.4-1.4 8.6-4-1.6z" fill="#78838f"/><path d="M7.4 7.2l5.8 4.6-4 8.4-5.2-4.6z" fill="#8d97a4"/></svg>',
  food:'<svg viewBox="0 0 24 24"><path d="M12 21V8.5" stroke="#8a9a3e" stroke-width="1.7" stroke-linecap="round"/><path d="M12 9.4c-2.9-.4-4.3-2.2-4.3-4.6 2.6-.5 4.3.9 4.3 4.6zM12 9.4c2.9-.4 4.3-2.2 4.3-4.6-2.6-.5-4.3.9-4.3 4.6zM12 14.6c-2.9-.4-4.3-2.2-4.3-4.6 2.6-.5 4.3.9 4.3 4.6zM12 14.6c2.9-.4 4.3-2.2 4.3-4.6-2.6-.5-4.3.9-4.3 4.6z" fill="#e8c25a"/><path d="M12 6.6c-1.3-1.6-1.3-3.4 0-5.1 1.3 1.7 1.3 3.5 0 5.1z" fill="#f2d67e" transform="translate(0,1)"/></svg>',
  cloth:'<svg viewBox="0 0 24 24"><path d="M8 3l4 2.4L16 3l4.6 3.2-2 3.4-1.4-.8V21H6.8V8.8l-1.4.8-2-3.2z" fill="#c9a3d6"/><path d="M12 5.4L16 3l4.6 3.2-2 3.4-1.4-.8" fill="#a87fbc"/><path d="M6.8 12h10.4M6.8 15.4h10.4M6.8 18.6h10.4" stroke="#8f67a6" stroke-width=".9" opacity=".7"/></svg>',
  tools:'<svg viewBox="0 0 24 24"><path d="M14.6 2.6l6.8 6.8-2.6 2.6-6.8-6.8z" fill="#b9c4d2"/><path d="M12 6.4L3.6 14.8a2.6 2.6 0 003.7 3.7L15.7 10z" fill="#a06a34"/><path d="M12 6.4L3.6 14.8a2.6 2.6 0 003.7 3.7L15.7 10z" fill="none" stroke="#6d4520" stroke-width=".8"/><path d="M14.6 2.6l2 2-2.2 2.2-2-2z" fill="#dfe6ee"/></svg>',
  flour:'<svg viewBox="0 0 24 24"><path d="M6.6 8.6h10.8l1.5 9a3 3 0 01-3 3.4H8.1a3 3.05 0 01-3-3.4z" fill="#efe4c8"/><path d="M6.6 8.6h10.8l.5 2.9H6.1z" fill="#d8c8a2"/><path d="M9.4 5c1.2 1.1 1.5 2.2 2.6 3.5C13.1 7.2 13.4 6.1 14.6 5" fill="#f8f1de"/><path d="M9.8 13.6h4.6M9.2 16.8h5.8" stroke="#c0ab7e" stroke-width="1.2" stroke-linecap="round"/></svg>',
  bread:'<svg viewBox="0 0 24 24"><path d="M4 14c0-4 3.5-6.6 8-6.6s8 2.6 8 6.6c0 2.7-1.5 4.5-3.8 4.5H7.8C5.5 18.5 4 16.7 4 14z" fill="#cf9347"/><path d="M4 14c0-4 3.5-6.6 8-6.6s8 2.6 8 6.6" fill="#e6b470"/><path d="M8.2 10.2c1 1.3 1 3.2 0 4.7M12 9.8c1 1.3 1 3.4 0 4.9M15.8 10.2c1 1.3 1 3.2 0 4.7" stroke="#a4682a" stroke-width="1.3" fill="none" stroke-linecap="round"/></svg>',
  scroll:'<svg viewBox="0 0 24 24"><path d="M6.4 3.4h11.2a2.2 2.2 0 012.2 2.2v12.8a2.2 2.2 0 01-2.2 2.2H6.4z" fill="#f0e7d1"/><path d="M6.4 3.4H4.2a2.2 2.2 0 000 4.4h2.2v12.6a2.2 2.2 0 002.2 2.2h9.6" fill="none" stroke="#c8b58c" stroke-width="1.7"/><path d="M9.6 8.4h6.6M9.6 11.6h6.6M9.6 14.8h4" stroke="#98876a" stroke-width="1.2" stroke-linecap="round"/></svg>',
  star:'<svg viewBox="0 0 24 24"><path d="M12 2.4l3 6.2 6.8.8-4.9 4.7 1.3 6.7L12 17.6l-6.2 3.2 1.3-6.7L2.2 9.4 9 8.6z" fill="#f2b45c"/><path d="M12 2.4l3 6.2 6.8.8-4.9 4.7" fill="none" stroke="#ffe4ad" stroke-width="1.1" stroke-linejoin="round"/></svg>',
  coin:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="9" fill="#e0a145"/><circle cx="12" cy="12" r="9" fill="none" stroke="#8d5f18" stroke-width="1.1"/><circle cx="12" cy="12" r="6.2" fill="none" stroke="#ffd98a" stroke-width="1.2" opacity=".85"/><path d="M12 7.6v8.8M9.6 9.6h4a1.9 1.9 0 010 3.8h-3.4a1.9 1.9 0 000 3.8h4" stroke="#8d5f18" stroke-width="1.3" fill="none" stroke-linecap="round"/></svg>',
  pop:'<svg viewBox="0 0 24 24"><circle cx="9" cy="7.6" r="3.6" fill="#e8b98f"/><path d="M2.6 20c0-3.9 2.9-6.6 6.4-6.6s6.4 2.7 6.4 6.6z" fill="#5f7fa8"/><circle cx="17.4" cy="9" r="2.7" fill="#d9a67c"/><path d="M14.4 20c0-3 1.6-5 4-5s3.2 1.6 3.2 4.2" fill="#4a6488"/></svg>',
  heart:'<svg viewBox="0 0 24 24"><path d="M12 20.4S3.6 15 3.6 9.2A4.4 4.4 0 0112 7a4.4 4.4 0 018.4 2.2c0 5.8-8.4 11.2-8.4 11.2z" fill="#f0685a"/></svg>',
  skull:'<svg viewBox="0 0 24 24"><path d="M12 2.6c-5 0-8.2 3.2-8.2 7.6 0 2.8 1.2 4.4 2.6 5.4v3.2c0 1.4 1 2.6 2.4 2.6h6.4c1.4 0 2.4-1.2 2.4-2.6v-3.2c1.4-1 2.6-2.6 2.6-5.4 0-4.4-3.2-7.6-8.2-7.6z" fill="#dfe4ec"/><circle cx="8.6" cy="10.4" r="2.2" fill="#2a2f3a"/><circle cx="15.4" cy="10.4" r="2.2" fill="#2a2f3a"/><path d="M10.6 15.4h2.8v5h-2.8z" fill="#2a2f3a"/></svg>',
  bolt:'<svg viewBox="0 0 24 24"><path d="M13.6 2L4.8 13.4h5.2L9.4 22l9.4-12h-5.8z" fill="#ffd166"/></svg>',
  leaf:'<svg viewBox="0 0 24 24"><path d="M20 4c0 9-5 14-11.4 14A5.6 5.6 0 013 12.4C3 6.6 9.6 4.6 20 4z" fill="#5fd69b"/><path d="M20 4C11 8 6.6 12.6 5 18" stroke="#2f8f63" stroke-width="1.3" fill="none"/></svg>',
  snow:'<svg viewBox="0 0 24 24"><path d="M12 2v20M3.4 7l17.2 10M20.6 7L3.4 17" stroke="#bfe0ff" stroke-width="1.7" stroke-linecap="round"/><path d="M12 6.4l-2-2M12 6.4l2-2M12 17.6l-2 2M12 17.6l2 2" stroke="#bfe0ff" stroke-width="1.5" stroke-linecap="round"/></svg>',
  sun:'<svg viewBox="0 0 24 24"><circle cx="12" cy="12" r="4.6" fill="#ffcf85"/><path d="M12 1.6v3M12 19.4v3M1.6 12h3M19.4 12h3M4.6 4.6l2.1 2.1M17.3 17.3l2.1 2.1M19.4 4.6l-2.1 2.1M6.7 17.3l-2.1 2.1" stroke="#ffcf85" stroke-width="1.7" stroke-linecap="round"/></svg>',
  cloud:'<svg viewBox="0 0 24 24"><path d="M7 18.4a4.2 4.2 0 01-.4-8.4 5.6 5.6 0 0110.7-1.2A3.9 3.9 0 0118 18.4z" fill="#a8b6c8"/></svg>',
  rain:'<svg viewBox="0 0 24 24"><path d="M7 14a4.2 4.2 0 01-.4-8.4A5.6 5.6 0 0117.3 4.4 3.9 3.9 0 0118 14z" fill="#8f9fb5"/><path d="M8 16.6l-1.2 4M12.4 16.6l-1.2 4M16.8 16.6l-1.2 4" stroke="#63a9ef" stroke-width="1.8" stroke-linecap="round"/></svg>',
};

/* ── procedural audio ─────────────────────────────────────────────────── */
const Audio_={
  ctx:null,master:null,amb:null,ambGain:null,enabled:true,ready:false,rainNode:null,rainGain:null,
  init(){
    if(this.ready)return;
    try{
      const AC=window.AudioContext||window.webkitAudioContext; if(!AC)return;
      this.ctx=new AC();
      this.master=this.ctx.createGain(); this.master.gain.value=.5; this.master.connect(this.ctx.destination);
      this.ambGain=this.ctx.createGain(); this.ambGain.gain.value=0; this.ambGain.connect(this.master);
      this.ready=true;
      this.startAmbient();
    }catch(e){this.ready=false;}
  },
  startAmbient(){
    const c=this.ctx;
    // warm pad: two detuned saws through a low-pass, very quiet
    const g=c.createGain(); g.gain.value=.055;
    const f=c.createBiquadFilter(); f.type="lowpass"; f.frequency.value=420; f.Q.value=.6;
    g.connect(f); f.connect(this.ambGain);
    [110,164.81,220].forEach((hz,i)=>{
      const o=c.createOscillator(); o.type=i===2?"triangle":"sawtooth"; o.frequency.value=hz;
      const og=c.createGain(); og.gain.value=i===2?.28:.4;
      const lfo=c.createOscillator(); lfo.frequency.value=.045+i*.017;
      const lg=c.createGain(); lg.gain.value=hz*.006;
      lfo.connect(lg); lg.connect(o.frequency); lfo.start();
      o.connect(og); og.connect(g); o.start();
    });
    this.ambGain.gain.setTargetAtTime(1,c.currentTime,3);
    // rain/wind noise bed
    const len=c.sampleRate*3, buf=c.createBuffer(1,len,c.sampleRate), d=buf.getChannelData(0);
    let last=0; for(let i=0;i<len;i++){const w=Math.random()*2-1;last=(last+.02*w)/1.02;d[i]=last*3.2;}
    const src=c.createBufferSource(); src.buffer=buf; src.loop=true;
    const bp=c.createBiquadFilter(); bp.type="bandpass"; bp.frequency.value=620; bp.Q.value=.5;
    this.rainGain=c.createGain(); this.rainGain.gain.value=0;
    src.connect(bp); bp.connect(this.rainGain); this.rainGain.connect(this.master); src.start();
    this.rainNode=bp;
  },
  setRain(v){ if(this.rainGain&&this.ready) this.rainGain.gain.setTargetAtTime(v*.16,this.ctx.currentTime,.6); },
  tone(freq,dur,type="sine",vol=.18,slide=0,delay=0){
    if(!this.ready||!this.enabled)return;
    const c=this.ctx,t=c.currentTime+delay;
    const o=c.createOscillator(),g=c.createGain();
    o.type=type;o.frequency.setValueAtTime(freq,t);
    if(slide)o.frequency.exponentialRampToValueAtTime(max(30,freq*slide),t+dur);
    g.gain.setValueAtTime(0,t);g.gain.linearRampToValueAtTime(vol,t+.008);
    g.gain.exponentialRampToValueAtTime(.0001,t+dur);
    o.connect(g);g.connect(this.master);o.start(t);o.stop(t+dur+.05);
  },
  noise(dur,vol=.2,freq=1200,q=1,type="bandpass",delay=0){
    if(!this.ready||!this.enabled)return;
    const c=this.ctx,t=c.currentTime+delay;
    const n=floor(c.sampleRate*dur), b=c.createBuffer(1,n,c.sampleRate), d=b.getChannelData(0);
    for(let i=0;i<n;i++)d[i]=(Math.random()*2-1)*(1-i/n);
    const s=c.createBufferSource();s.buffer=b;
    const f=c.createBiquadFilter();f.type=type;f.frequency.value=freq;f.Q.value=q;
    const g=c.createGain();g.gain.value=vol;
    s.connect(f);f.connect(g);g.connect(this.master);s.start(t);
  },
  ui(){this.tone(880,.05,"triangle",.05);},
  uiBig(){this.tone(520,.09,"triangle",.09);this.tone(780,.11,"triangle",.05,1,.03);},
  chop(){this.noise(.14,.22,900,.9);this.tone(150,.09,"square",.05,.5);},
  mine(){this.noise(.16,.2,2400,1.6,"highpass");this.tone(90,.1,"square",.06,.4);},
  build(){this.tone(220,.07,"square",.07,1.6);this.noise(.09,.13,700,1.1);},
  coin(){this.tone(1180,.07,"triangle",.09);this.tone(1620,.11,"triangle",.06,1,.045);},
  harvest(){this.noise(.2,.14,3200,1.2,"highpass");},
  err(){this.tone(180,.13,"sawtooth",.07,.6);},
  bell(){[523,659,784].forEach((f,i)=>this.tone(f,.5,"sine",.09,1,i*.09));},
  doom(){this.tone(90,1.1,"sawtooth",.11,.55);this.noise(.9,.13,300,.7,"lowpass");},
  death(){this.tone(320,.5,"sine",.1,.35);this.noise(.4,.09,500,.8);},
  levelup(){[440,554,659,880].forEach((f,i)=>this.tone(f,.3,"triangle",.075,1,i*.06));},
  fanfare(){[392,523,659,784,1046].forEach((f,i)=>this.tone(f,.42,i>2?"sine":"triangle",.085,1,i*.11));
            this.tone(196,.9,"sine",.05,1,.34); this.tone(294,.7,"triangle",.04,1,.45);},
};

/* ── canvas setup ─────────────────────────────────────────────────────── */
const cv=$("#game");
let ctx=cv.getContext("2d",{alpha:false});
let NOFX=false;
let VW=0,VH=0,DPR=1;
function resize(){
  DPR=Math.min(window.devicePixelRatio||1,2);
  VW=window.innerWidth; VH=window.innerHeight;
  cv.width=Math.round(VW*DPR); cv.height=Math.round(VH*DPR);
  cv.style.width=VW+"px"; cv.style.height=VH+"px";
  ctx.setTransform(DPR,0,0,DPR,0,0);
}
window.addEventListener("resize",resize); resize();

/*═══════════════════════════════════════════════════════════════════════════════
  Part 2 · definitions: biomes, nodes, buildings, crops, recipes
═══════════════════════════════════════════════════════════════════════════════*/

const MAP_W=104, MAP_H=104;
const TW=64, TH=32;                       // isometric tile size
const idx=(x,y)=>y*MAP_W+x;
const inb=(x,y)=>x>=0&&y>=0&&x<MAP_W&&y<MAP_H;

/* time base — declared here because both the world rules and the clock build on it */
const MIN_PER_SEC=6;                  // game minutes per real second at 1×
const SPEEDS=[0,1,2.5,6.5];
const DAY_MIN=24*60;
const DT_DAY=DAY_MIN/MIN_PER_SEC;     // sim-seconds per game day (240)

/* biomes */
const B={DEEP:0,WATER:1,SAND:2,GRASS:3,FOREST:4,MEADOW:5,DIRT:6,ROCK:7,PEAK:8};
const BNAME=["Água profunda","Água","Areia","Campo","Floresta","Prado","Terra","Rochedo","Pico"];
/* overlays */
const O={NONE:0,ROAD:1,FARM:2};

/* base colours per biome — [spring, summer, autumn, winter] */
const BIOME_COL=[
  /*DEEP  */[[26,58,86],[22,52,82],[24,54,80],[30,54,74]],
  /*WATER */[[46,102,132],[38,94,128],[44,96,120],[62,92,110]],
  /*SAND  */[[206,186,138],[214,193,142],[200,174,124],[216,214,206]],
  /*GRASS */[[96,142,72],[84,138,60],[138,138,66],[196,204,206]],
  /*FOREST*/[[62,104,56],[52,96,48],[110,96,48],[160,172,176]],
  /*MEADOW*/[[122,158,78],[110,152,66],[158,150,72],[198,206,204]],
  /*DIRT  */[[126,96,66],[120,92,62],[124,96,62],[172,166,158]],
  /*ROCK  */[[116,116,122],[110,110,116],[118,112,108],[186,190,196]],
  /*PEAK  */[[142,144,152],[138,140,148],[146,144,146],[226,230,238]],
];
/* movement cost & passability */
const BCOST=[99,99,1.45,1.0,1.6,1.05,1.15,2.4,99];
const BPASS=[0,0,1,1,1,1,1,1,0];

/* resource node kinds */
const N={OAK:1,PINE:2,BIRCH:3,BUSH:4,BOULDER:5,ORE:6,FLAX:7,DEADTREE:8};
const NODEDEF={
  [N.OAK]:    {name:"Carvalho",   work:5.0, yield:{wood:6}, hp:1, sway:.9,  h:34},
  [N.PINE]:   {name:"Pinheiro",   work:5.6, yield:{wood:7}, hp:1, sway:.55, h:44},
  [N.BIRCH]:  {name:"Bétula",     work:4.2, yield:{wood:4}, hp:1, sway:1.1, h:38},
  [N.BUSH]:   {name:"Arbusto de bagas", work:1.6, yield:{food:3}, hp:0, sway:1.4, h:13, regrow:9},
  [N.BOULDER]:{name:"Rochedo",    work:7.0, yield:{stone:6}, hp:1, sway:0,  h:20},
  [N.ORE]:    {name:"Veio de minério", work:9.0, yield:{stone:5,coin:9}, hp:1, sway:0, h:18},
  [N.FLAX]:   {name:"Linho silvestre", work:1.4, yield:{cloth:2}, hp:0, sway:1.6, h:14, regrow:7},
  [N.DEADTREE]:{name:"Árvore seca", work:3.0, yield:{wood:3}, hp:1, sway:.4, h:30},
};

/* resources */
const R={wood:"wood",stone:"stone",food:"food",cloth:"cloth",tools:"tools",coin:"coin"};
const RESDEF=[
  {k:"wood", name:"Madeira",     col:"#a06a34", icon:"wood",  base:8},
  {k:"stone",name:"Pedra",       col:"#9aa4b2", icon:"stone", base:9},
  {k:"food", name:"Comida",      col:"#e8c25a", icon:"food",  base:14},
  {k:"cloth",name:"Tecido",      col:"#c9a3d6", icon:"cloth", base:16},
  {k:"tools",name:"Ferramentas", col:"#b9c4d2", icon:"tools", base:26},
  {k:"flour",name:"Farinha",     col:"#e6d7ae", icon:"flour", base:19, mini:true},
  {k:"bread",name:"Pão",         col:"#d79a4e", icon:"bread", base:24, mini:true},
  {k:"coin", name:"Moedas",      col:"#e0a145", icon:"coin",  base:1},
];
const RESIX={}; RESDEF.forEach((r,i)=>RESIX[r.k]=i);

/* categories */
const CATS=[
  {id:"ordem", name:"Ordens"},
  {id:"base",  name:"Base"},
  {id:"comida",name:"Comida"},
  {id:"ind",   name:"Indústria"},
  {id:"def",   name:"Defesa"},
  {id:"belo",  name:"Belo"},
  {id:"pres",  name:"Prestígio"},
];

/* building definitions */
const BDEF={
  road:    {name:"Estrada",        cat:"base", w:1,h:1, cost:{stone:1},              hp:120, desc:"Caminho compactado. Colonos atravessam 2× mais rápido.", key:"Q", ovr:O.ROAD},
  stock:   {name:"Depósito",       cat:"base", w:3,h:2, cost:{wood:26},              hp:260, store:340, desc:"Armazém coberto. Aumenta a capacidade de estoque da colônia.", key:"E"},
  house:   {name:"Casa",           cat:"base", w:2,h:2, cost:{wood:34,stone:10},     hp:300, beds:4,  desc:"Abriga 4 colonos. Dormir aqui restaura energia e protege do frio.", key:"R"},
  well:    {name:"Poço",           cat:"base", w:1,h:1, cost:{stone:16},             hp:180, desc:"Fonte de água para apagar incêndios e +humor nas redondezas.", key:"T", near:"land"},
  farm:    {name:"Fazenda",        cat:"comida",w:3,h:3,cost:{wood:12},              hp:140, desc:"Solo arado. Escolha a cultura; cresce conforme a estação.", key:"F", soil:true, ovr:O.FARM},
  orchard: {name:"Pomar",          cat:"comida",w:2,h:2,cost:{wood:20,food:6},       hp:180, desc:"Árvores frutíferas. Produz comida lentamente por anos, sem replantio.", key:"G", soil:true, ovr:O.FARM},
  workshop:{name:"Oficina",        cat:"ind",  w:2,h:2, cost:{wood:30,stone:14},     hp:280, craft:1, desc:"Artesãos transformam matéria-prima em ferramentas e bens.", key:"V"},
  mine:    {name:"Mina",           cat:"ind",  w:2,h:2, cost:{wood:20,stone:6},      hp:300, desc:"Extrai pedra continuamente. Precisa de rochedo por perto.", key:"B", near:"rock"},
  market:  {name:"Mercado",        cat:"ind",  w:2,h:2, cost:{wood:48,stone:28,tools:2}, hp:300, desc:"Atrai caravanas e gera moedas com impostos. Melhora os preços.", key:"N"},
  infirm:  {name:"Enfermaria",     cat:"ind",  w:2,h:2, cost:{wood:36,cloth:12},     hp:260, desc:"Curandeiros tratam feridos e doentes. Reduz mortes.", key:"I"},
  wall:    {name:"Muro de pedra",  cat:"def",  w:1,h:1, cost:{stone:7},              hp:520, block:true, desc:"Bloqueia o avanço de invasores e lobos.", key:"Z"},
  tower:   {name:"Torre de vigia", cat:"def",  w:1,h:1, cost:{wood:26,stone:22},     hp:400, militia:2, desc:"Posto para 2 milicianos. Aumenta o alcance de defesa.", key:"X"},
  bonfire: {name:"Fogueira",       cat:"belo", w:1,h:1, cost:{wood:9,stone:4},       hp:120, mood:9, light:150, desc:"Ponto de encontro. +humor e luz quente à noite.", key:"C"},
  lamp:    {name:"Lampião",        cat:"belo", w:1,h:1, cost:{wood:5,tools:1},       hp:90,  light:110, desc:"Ilumina caminhos durante a noite.", key:"L"},
  statue:  {name:"Monumento",      cat:"belo", w:2,h:2, cost:{stone:60,tools:4},     hp:500, mood:16, prestige:1, desc:"Símbolo da colônia. Grande +humor permanente e rende 1 ponto de prestígio.", key:"K"},
  mill:    {name:"Moinho d'Água",  cat:"pres", w:2,h:2, cost:{wood:30,stone:22},     hp:320, craft:1, pres:1, near:"water", key:"J",
            desc:"A roda gira e mói o grão em farinha. Rola mais perto de água e produz sozinho."},
  bakery:  {name:"Forno Comunal",  cat:"pres", w:2,h:2, cost:{wood:26,stone:30},     hp:300, craft:1, pres:1, mood:5, key:"P",
            desc:"Assa farinha em pão. Pão no estoque alimenta melhor e ergue o humor."},
  barn:    {name:"Celeiro Grande", cat:"pres", w:3,h:2, cost:{wood:38,stone:18},     hp:340, store:820, pres:1, key:"D",
            desc:"Enorme armazém abovedado. Quase triplica a capacidade de estoque."},
  academy: {name:"Escola",         cat:"pres", w:2,h:2, cost:{wood:44,stone:26,cloth:10}, hp:300, pres:2, mood:8, teach:1, key:"A",
            desc:"Mestres ensinam ofícios. Todas as habilidades da colônia evoluem mais rápido."},
  garrison:{name:"Quartel",        cat:"pres", w:2,h:2, cost:{wood:34,stone:34,tools:2},  hp:460, militia:4, pres:2, key:"U",
            desc:"Milicianos treinados: +4 postos e defesas mais rápidas contra invasores."},
};
const BORDER=["road","stock","house","well","farm","orchard","workshop","mine","market","infirm","wall","tower","bonfire","lamp","statue","mill","bakery","barn","academy","garrison"];

/* designation tools (not buildings) */
const TOOLS={
  chop:  {name:"Cortar árvores", cat:"ordem", desc:"Marque uma área para derrubar árvores e obter madeira.", key:"1", col:"#a06a34", drag:true},
  mine:  {name:"Minerar rochas", cat:"ordem", desc:"Marque rochedos e veios para extrair pedra.", key:"2", col:"#9aa4b2", drag:true},
  gather:{name:"Coletar",        cat:"ordem", desc:"Colha arbustos de bagas e linho silvestre.", key:"3", col:"#e8c25a", drag:true},
  demo:  {name:"Demolir",        cat:"ordem", desc:"Remova construções, estradas e vegetação marcadas.", key:"4", col:"#f0685a", drag:true},
  cancel:{name:"Cancelar ordem", cat:"ordem", desc:"Cancele marcações numa área.", key:"5", col:"#8b98ad", drag:true},
};
const TOOLORDER=["chop","mine","gather","demo","cancel"];

/* crops */
const CROPS={
  wheat:  {name:"Trigo",  plant:0, harvest:2, grow:8, yield:{food:14}, col:[["#7d9a3c","#a8c25a"],["#d9b84e","#f0d67a"]], desc:"Plantio na primavera, colheita no verão. Base da dieta."},
  corn:   {name:"Milho",  plant:1, harvest:2, grow:7, yield:{food:11}, col:[["#5f9440","#86bb58"],["#e0c15c","#f5dd8a"]], desc:"Ciclo mais curto, plantado no verão. Menor rendimento."},
  flax:   {name:"Linho",  plant:0, harvest:2, grow:9, yield:{cloth:7}, col:[["#6f9f6a","#9ec98f"],["#b9a7d8","#d9ccf0"]], desc:"Fibras para tecido. Essencial contra o inverno."},
  turnip: {name:"Nabo",   plant:2, harvest:3, grow:5, yield:{food:9},  col:[["#7ea356","#a5c877"],["#c8b48c","#e6d6b4"]], desc:"Resistente ao frio — última chance antes do inverno."},
};
const CROPORDER=["wheat","corn","flax","turnip"];

/* workshop recipes */
const RECIPES={
  tools:  {name:"Ferramentas", in:{wood:3,stone:2}, out:{tools:1}, time:7,  bld:["workshop"], desc:"Cada colono com ferramenta trabalha 30% mais rápido."},
  brew:   {name:"Barril de cerveja", in:{food:6}, out:{}, time:9, buff:"festival", bld:["workshop"], desc:"Inicia um festival de 3 dias: +humor para toda a colônia."},
  furnish:{name:"Mobília", in:{wood:4,cloth:2}, out:{}, time:8, furnish:1, bld:["workshop"], desc:"Melhora uma casa (até 3). Colonos descansam melhor e ficam mais felizes."},
  flour:  {name:"Saco de farinha", in:{food:5}, out:{flour:3}, time:6, bld:["mill"], desc:"Mói o grão. O moinho repete o serviço sozinho enquanto houver comida no estoque."},
  bread:  {name:"Fornada de pão", in:{flour:3,food:2}, out:{bread:2}, time:8, bld:["bakery"], desc:"Pão assado: quem come pão fica mais feliz e aguenta mais frio."},
};
const RECIPEORDER=["tools","brew","furnish","flour","bread"];

/* seasons */
const SEASONS=[
  {name:"Primavera", short:"PRI", col:"#7ec87e", temp:[8,19],  grow:1.00, desc:"Plantio. O vale desperta."},
  {name:"Verão",     short:"VER", col:"#f0c454", temp:[16,31], grow:1.25, desc:"Crescimento acelerado, tempestades."},
  {name:"Outono",    short:"OUT", col:"#e08a44", temp:[6,17],  grow:0.75, desc:"Colheita. Prepare o estoque."},
  {name:"Inverno",   short:"INV", col:"#8fc4ec", temp:[-14,2], grow:0.00, desc:"Nada cresce. Frio mata quem não tem abrigo."},
];
const SEASON_DAYS=12;
const WEATHER={
  clear: {name:"Céu limpo",  icon:"sun",   grow:1.00, speed:1.00, light:1.00},
  clouds:{name:"Nublado",    icon:"cloud", grow:0.95, speed:1.00, light:0.80},
  rain:  {name:"Chuva",      icon:"rain",  grow:1.30, speed:0.85, light:0.58},
  storm: {name:"Tempestade", icon:"bolt",  grow:1.20, speed:0.70, light:0.40},
  snow:  {name:"Nevasca",    icon:"snow",  grow:0.00, speed:0.62, light:0.62},
  fog:   {name:"Névoa",      icon:"cloud", grow:1.00, speed:0.90, light:0.66},
};

/* ── game modes ───────────────────────────────────────────────────────── */
function builtOf(k){let n=0;for(const b of G.buildings)if(b&&!b.dead&&b.built>=1&&b.def===k)n++;return n;}
function defenses(){let n=0;for(const b of G.buildings)if(b&&!b.dead&&b.built>=1&&(b.def==="wall"||b.def==="tower"))n+=b.w*b.h;return n;}

const MODES={
  livre:{
    name:"Colônia Livre", kick:"Sandbox", col:"#7ec87e", icon:"leaf",
    desc:"Sem prazos, sem fim. Construa o vale que quiser — pedidos pontuais rendem prestígio, mas nada encerra a partida.",
    start:{wood:55,stone:20,food:60,cloth:8,tools:1,coin:35},
    raid:1, immigration:1, caravan:1, vol:1, harsh:0, autosave:true, policy:"side",
    sub:"4 colonos · primavera do ano 1",
  },
  carta:{
    name:"Carta do Senhor", kick:"Campanha", col:"#f2b45c", icon:"scroll",
    desc:"Seis ordens de um senhor feudal, uma após outra, com prazo. Cumpra-as e o vale será seu — a campanha tem final.",
    start:{wood:60,stone:24,food:66,cloth:10,tools:2,coin:70},
    raid:1, immigration:1, caravan:1, vol:1, harsh:0, autosave:true, policy:"chain",
    sub:"6 contratos · o relógio do senhor corre",
  },
  duro:{
    name:"Vale Implacável", kick:"Difícil", col:"#f0685a", icon:"skull",
    desc:"Estoque mínimo, frio que mata, invasões em dobro e nenhum imigrante. Salve só quando quiser — sobreviva três invernos.",
    start:{wood:18,stone:6,food:26,cloth:2,tools:0,coin:10},
    raid:2, immigration:0, caravan:0.7, vol:1.2, harsh:1, autosave:false, policy:"side", tight:0.75,
    win:{day:SEASON_DAYS*4*3},
    sub:"4 colonos · fome no primeiro mês",
  },
  rota:{
    name:"Rota das Caravanas", kick:"Economia", col:"#63a9ef", icon:"coin",
    desc:"O vale vive em paz. Caravanas todo dia, preços que saltam e uma fortuna a fazer: acumule 1.200 moedas.",
    start:{wood:42,stone:14,food:52,cloth:6,tools:1,coin:150},
    raid:0, immigration:1, caravan:2.2, vol:2.2, harsh:0, autosave:true, policy:"trade",
    win:{coin:1200},
    sub:"paz permanente · mercados voláteis",
  },
};
const MODEORDER=["livre","carta","duro","rota"];
function MD(){return MODES[G.mode]||MODES.livre;}

/* ── contracts / objectives ───────────────────────────────────────────── */
/* each target() returns [progress, requirement] — both shown in the panel */
const CONTRACTS={
  /* campaign: a chain told as a story */
  c_teto:{title:"Teto para todos", from:"Senhor Aldredo", days:20,
    brief:"Meus camponeses dormem no acampamento. Erga casas até oito leitos antes que o frio chegue.",
    target:()=>[min(8,G.housingCap),8],
    reward:{coin:90,pres:1}, penalty:{coin:30,mood:12}},
  c_celeiro:{title:"O celeiro do senhor", from:"Senhor Aldredo", days:22,
    brief:"Um inverno faminto arrasou a última vila. Encha meu celeiro: 180 unidades de comida.",
    target:()=>[min(180,G.stock.food),180],
    reward:{coin:120,pres:1,tools:3}, penalty:{coin:50,mood:14}},
  c_ferr:{title:"Ferro na terra", from:"O ferroeiro Delfim", days:20,
    brief:"Tenha seis ferramentas no estoque — terra lavrada a mão não paga o meu pedágio.",
    target:()=>[min(6,G.stock.tools),6],
    reward:{coin:110,pres:1,cloth:10}, penalty:{coin:40,mood:8}},
  c_moinho:{title:"Moinho e forno", from:"Senhora Beatrix", days:26,
    brief:"Grão sem pão é dinheiro jogado fora. Erga um moinho junto à água e um forno ao lado.",
    target:()=>[builtOf("mill")+builtOf("bakery"),2],
    reward:{coin:140,pres:2}, penalty:{coin:60,mood:10}},
  c_muro:{title:"Pedra contra salteadores", from:"Capitão Vilar", days:24,
    brief:"Cerce o vale: dezoito quadros entre muros e torres, e repila duas ondas.",
    target:()=>[defenses(),18],
    reward:{coin:160,pres:2,tools:4}, penalty:{coin:70,mood:12,threat:10}},
  c_tributo:{title:"O tributo final", from:"Senhor Aldredo", days:30,
    brief:"Entregue quatrocentas moedas e o vale inteiro passa a ser seu, por escritura.",
    target:()=>[min(400,G.stock.coin),400], cost:{coin:400},
    reward:{pres:3}, penalty:{coin:80,mood:16}},

  /* side requests — offered one at a time in the other modes */
  s_farinha:{title:"Farinha para o inverno", from:"O moleiro Caio", days:18,
    brief:"Acumule 30 sacos de farinha antes que a neve feche os caminhos.",
    target:()=>[min(30,G.stock.flour+G.stock.bread*2),30], reward:{coin:70,pres:1}, penalty:{mood:6}},
  s_pao:{title:"Pão quente no mercado", from:"A padroeira Otília", days:16,
    brief:"Dez pães assados no forno comunal. O cheiro já traz freguesia.",
    target:()=>[min(10,G.stock.bread),10], reward:{coin:80,pres:1}, penalty:{mood:6}},
  s_festa:{title:"Um dia de festa", from:"O bufão Nicanor", days:14,
    brief:"Cerveja no salão! Celebre um festival e o vale inteiro lembra do seu nome.",
    target:()=>[G.buff.festival>0?1:0,1], reward:{coin:60,pres:1}, penalty:{mood:8}},
  s_mercado:{title:"Praça de trocas", from:"A guilda mercante", days:20,
    brief:"Construa um mercado permanente e as caravanas terão onde atracar.",
    target:()=>[builtOf("market"),1], reward:{coin:90,pres:1}, penalty:{coin:20}},
  s_pop:{title:"Vinte almas", from:"O cronista", days:34,
    brief:"Uma vila só existe quando tem gente. Chegue a vinte colonos vivos.",
    target:()=>[min(20,aliveCols().length),20], reward:{coin:120,pres:2}, penalty:{mood:6}},
  s_defesa:{title:"Cercar o coreto", from:"Capitão Vilar", days:22,
    brief:"Doze quadros de muro ou torre. Lobo não escala pedra.",
    target:()=>[min(12,defenses()),12], reward:{coin:80,pres:1}, penalty:{threat:8}},
  s_escola:{title:"Mestres para os filhos", from:"A abadessa Senara", days:30,
    brief:"Erga a escola. Habilidades treinadas valem mais que ouro enterrado.",
    target:()=>[builtOf("academy"),1], reward:{pres:2,coin:60}, penalty:{mood:5}},
  s_monumento:{title:"Um marco de pedra", from:"O escultor Cosme", days:26,
    brief:"Erga um monumento. Colônia sem memória é só um acampamento longo.",
    target:()=>[builtOf("statue"),1], reward:{pres:2,coin:70}, penalty:{mood:8}},
  s_comercio:{title:"Rota comercial", from:"A guilda mercante", days:24,
    brief:"Feche quinze operações de compra ou venda com as caravanas.",
    target:()=>[min(15,G.stats.traded),15], reward:{coin:130,pres:1}, penalty:{coin:25}},
  s_inverno:{title:"Isoar o inverno", from:"O velho Henrique", days:26,
    brief:"Dez peças de tecido no estoque antes da nevasca. Ninguém sobrevive nu.",
    target:()=>[min(10,G.stock.cloth),10], reward:{coin:70,pres:1}, penalty:{mood:8}},
  s_horta:{title:"Pomar permanente", from:"A fruteira Luzia", days:22,
    brief:"Dois pomares plantados. Fruta toda estação, sem arar de novo.",
    target:()=>[min(2,builtOf("orchard")),2], reward:{coin:75,pres:1,food:30}, penalty:{mood:5}},
  s_oficina:{title:"Duas oficinas", from:"O ferreiro Delfim", days:20,
    brief:"Ferramenta boa custa ofício. Tenha duas oficinas funcionando.",
    target:()=>[min(2,builtOf("workshop")),2], reward:{coin:80,pres:1,tools:2}, penalty:{mood:5}},
  s_povo:{title:"Quatorze almas", from:"O cronista", days:28,
    brief:"Catorze colonos vivos: o mínimo para uma roda de conversa.",
    target:()=>[min(14,aliveCols().length),14], reward:{coin:90,pres:1}, penalty:{mood:5}},
  s_ouro:{title:"Cofre gordo", from:"O tesoureiro", days:26,
    brief:"Quatrocentas moedas guardadas. Imprevistos têm sempre preço.",
    target:()=>[min(400,G.stock.coin),400], reward:{pres:2}, penalty:{coin:30}},
};
const CAMPAIGN=["c_teto","c_celeiro","c_ferr","c_moinho","c_muro","c_tributo"];
const SIDEPOOL=["s_pop","s_defesa","s_mercado","s_farinha","s_pao","s_festa","s_comercio","s_escola","s_monumento","s_inverno","s_horta","s_oficina","s_povo","s_ouro"];
const TRADEPOOL=["s_comercio","s_ouro","s_mercado","s_farinha","s_pao","s_horta","s_oficina","s_inverno"];

/*─── prestige ───────────────────────────────────────────────────────────*/
function isUnlocked(k){const d=BDEF[k];return !d||!d.pres||!!G.unlocked[k];}
function lockedDefs(){return BORDER.filter(k=>BDEF[k].pres&&!G.unlocked[k]);}
function addPrestige(n,why){
  if(!n)return;
  G.prestige+=n; G.prestigeEarned=(G.prestigeEarned||0)+n;
  notify("Prestígio +"+n,(why||"A colônia ganha fama na região.")+" Gaste em novas técnicas (tecla O).","epic");
  if(rpTab==="obj")renderRight();
}
function unlockBuilding(k){
  const d=BDEF[k];
  if(!d||!d.pres||G.unlocked[k])return false;
  if(G.prestige<d.pres){hint("Prestígio insuficiente — faltam "+(d.pres-G.prestige)+".");Audio_.err();return false;}
  G.prestige-=d.pres; G.unlocked[k]=true;
  Audio_.bell();
  notify("Nova técnica",""+d.name+" liberada na aba Prestígio do menu de construção.","good");
  buildMenu(); if(rpTab==="obj")renderRight();
  return true;
}

/*─── contracts ──────────────────────────────────────────────────────────*/
const CONTRACT_GATE={
  s_farinha:()=>builtOf("mill")>0||!!G.unlocked.mill,
  s_pao:()=>builtOf("bakery")>0||!!G.unlocked.bakery,
  s_escola:()=>G.prestige>0||!!G.unlocked.academy||builtOf("academy")>0,
  s_monumento:()=>G.stock.stone>=20||builtOf("statue")>0,
  s_pop:()=>!!MD().immigration,          // 20 colonos é inviável sem imigração
  s_defesa:()=>!!MD().raid,
};
function contractPool(){
  const m=MD();
  return m.policy==="trade"?TRADEPOOL:SIDEPOOL;
}
function offerSide(){
  const used=new Set(G.obj.history.map(h=>h.id||h));
  let pool=contractPool().filter(id=>!used.has(id)&&(!CONTRACT_GATE[id]||CONTRACT_GATE[id]()));
  if(!pool.length){used.clear();pool=contractPool().filter(id=>!CONTRACT_GATE[id]||CONTRACT_GATE[id]());}
  if(!pool.length)return;
  startContract(pick(pool));
}
function startContract(id){
  const c=CONTRACTS[id]; if(!c)return;
  const days=max(4,round(c.days*(MD().tight||1)));
  G.obj.active={id,start:G.t.day,due:G.t.day+days};
  banner("CONTRATO",""+c.title);
  notify("Contrato: "+c.title,c.from+" — "+c.brief+" Prazo: "+days+" dias.","info");
  Audio_.bell();
  renderRight(); updateGoalBar();
}
function contractProgress(){
  const a=G.obj.active; if(!a)return null;
  const c=CONTRACTS[a.id]; if(!c)return null;
  let cur=0,need=1;
  try{const r=c.target();cur=r[0];need=r[1]||1;}catch(e){cur=0;need=1;}
  cur=max(0,min(need,cur));
  return {a,c,cur,need,pct:cur/need,left:a.due-G.t.day,late:G.t.day>a.due};
}
function rewardText(rw){
  const b=[];
  if(rw.coin)b.push(rw.coin+" moedas");
  if(rw.tools)b.push(rw.tools+" ferramentas");
  if(rw.cloth)b.push(rw.cloth+" tecido");
  if(rw.food)b.push(rw.food+" comida");
  if(rw.pres)b.push(rw.pres+" prestígio");
  return b.join(" · ")||"gratidão do vale";
}
function afterContract(){
  const m=MD();
  if(m.policy==="chain"){
    G.obj.chain++;
    if(G.obj.chain>=CAMPAIGN.length){finishCampaign();return;}
    G.obj.cooldown=2;
  } else G.obj.cooldown=randInt(4,9);
  updateGoalBar();
}
function completeContract(){
  const p=contractProgress(); if(!p)return;
  const {a,c}=p;
  G.obj.active=null; G.obj.done++; G.stats.contracts++;
  G.obj.history.push({id:a.id,day:G.t.day,ok:1});
  if(c.cost)for(const k in c.cost)G.stock[k]=max(0,(G.stock[k]|0)-c.cost[k]);
  const rw=c.reward||{};
  if(rw.coin)G.stock.coin+=rw.coin;
  if(rw.tools)addStock("tools",rw.tools);
  if(rw.cloth)addStock("cloth",rw.cloth);
  if(rw.food)addStock("food",rw.food);
  for(const cc of aliveCols())cc.mood=min(100,cc.mood+10);
  banner("CONTRATO CUMPRIDO",""+c.title);
  notify("Contrato cumprido","“"+c.title+"” entregue a "+c.from+". Pagaram: "+rewardText(rw)+".","epic");
  Audio_.fanfare?Audio_.fanfare():Audio_.bell();
  if(rw.pres)addPrestige(rw.pres,c.title+" reconhecido");
  afterContract();
}
function failContract(){
  const p=contractProgress(); if(!p)return;
  const {a,c}=p;
  G.obj.active=null; G.obj.failed++;
  G.obj.history.push({id:a.id,day:G.t.day,ok:0});
  const pen=c.penalty||{};
  if(pen.coin)G.stock.coin=max(0,G.stock.coin-pen.coin);
  if(pen.mood)for(const cc of aliveCols())cc.mood=max(0,cc.mood-pen.mood);
  if(pen.threat)G.threat=clamp(G.threat+pen.threat,0,100);
  G.moodShock=(G.moodShock||0)+8;
  banner("CONTRATO PERDIDO",""+c.title);
  notify("Prazo vencido","“"+c.title+"” não foi entregue a "+c.from+". Perda: "+(pen.coin?pen.coin+" moedas ":"")+(pen.mood?"humor da colônia ":"")+(pen.threat?"os invasores se aproximam":"reputação manchada")+".","bad");
  Audio_.doom();
  afterContract();
}
function finishCampaign(){
  const perfect=G.obj.failed===0;
  G.obj.cooldown=0;
  notify("Escritura assinada",perfect?"Nenhum prazo perdido. O senhor entrega o vale sem discussão.":"O senhor aceita a escritura, resmungando.",perfect?"epic":"good");
  gameOver(true);
}
function contractTick(){
  if(G.over)return;
  const m=MD();
  if(!G.obj.active){
    if(G.obj.cooldown>0){G.obj.cooldown--;}
    else if(G.t.day>=2){
      if(m.policy==="chain")startContract(CAMPAIGN[min(G.obj.chain,CAMPAIGN.length-1)]);
      else offerSide();
    }
    return;
  }
  const p=contractProgress();
  if(!p){G.obj.active=null;return;}
  if(p.pct>=1){completeContract();return;}
  if(p.late){failContract();return;}
  if(p.left<=3&&p.left>0&&!G.obj.active._warned){
    G.obj.active._warned=true;
    notify("Prazo apertado","Faltam "+p.left+" dia(s) para “"+p.c.title+"” ("+p.cur+"/"+p.need+").","bad");
  }
  updateGoalBar();
}
function modeWin(){
  const w=MD().win;
  if(!w)return false;
  if(w.coin&&G.stock.coin>=w.coin)return true;
  if(w.day&&G.t.day>=w.day)return true;
  return false;
}

/* ── objective strip in the HUD ───────────────────────────────────────── */
function updateGoalBar(){
  const bar=$("#goalbar"); if(!bar)return;
  const p=contractProgress();
  if(!p||G.over){bar.classList.remove("on");return;}
  bar.classList.add("on");
  bar.classList.toggle("due",p.left<=3);
  const chain=MD().policy==="chain";
  $("#gbIco").innerHTML=ICONS[p.left<=3?"skull":(chain?"scroll":"star")];
  $("#gbTitle").textContent=p.c.title;
  $("#gbFrom").textContent=(chain?"ordem "+min(G.obj.chain+1,CAMPAIGN.length)+" de "+CAMPAIGN.length+" · ":"")+p.c.from;
  $("#gbFill").style.width=round(p.pct*100)+"%";
  $("#gbVal").textContent=p.cur+"/"+p.need;
  $("#gbDue").textContent=p.left>0?p.left+(p.left===1?" dia":" dias"):"vencido";
}

/* colonist names */
const NAMES_M=["Afonso","Bento","Caio","Duarte","Estêvão","Fausto","Gil","Heitor","Inácio","Joaquim","Lourenço","Matias","Nuno","Otávio","Pero","Quirino","Rui","Simão","Tiago","Ulisses","Vasco","Xavier"];
const NAMES_F=["Adélia","Beatriz","Cecília","Dulce","Elvira","Filipa","Guiomar","Helena","Inês","Josefa","Leonor","Mafalda","Nair","Ofélia","Palma","Quitéria","Rosa","Salomé","Teresa","Ursula","Vera","Zilda"];
const SURNAMES=["do Vale","Ferreira","Monteiro","Almeida","Ribeiro","Coutinho","Sampaio","Nogueira","Barreto","Vasques","Antunes","Macedo","Peixoto","Quaresma","Sales","Teixeira","Vilar","Bittar","Moreira","Andrade"];
const TRAIT=[
  {id:"trab", name:"Trabalhador",  desc:"+20% velocidade de trabalho", col:"#5fd69b"},
  {id:"lent", name:"Preguiçoso",   desc:"-20% velocidade de trabalho", col:"#f0685a"},
  {id:"fort", name:"Forte",        desc:"+40% carga e dano",           col:"#63a9ef"},
  {id:"aleg", name:"Alegre",       desc:"humor base +15",              col:"#f2b45c"},
  {id:"tris", name:"Melancólico",  desc:"humor base -15",              col:"#a98bf0"},
  {id:"comi", name:"Comilão",      desc:"consome 50% mais comida",     col:"#e8c25a"},
  {id:"verd", name:"Mão verde",    desc:"+50% rendimento agrícola",    col:"#7ec87e"},
  {id:"brav", name:"Bravo",        desc:"não foge em combate, +dano",  col:"#ef8f5a"},
  {id:"medr", name:"Medroso",      desc:"foge de qualquer ameaça",     col:"#8b98ad"},
  {id:"notu", name:"Notívago",     desc:"trabalha bem à noite",        col:"#7f9fd6"},
];

/*═══════════════════════════════════════════════════════════════════════════════
  Part 3 · world generation
═══════════════════════════════════════════════════════════════════════════════*/

const G={
  seed:0, rng:null,
  bio:null,hgt:null,moi:null,fer:null,ovr:null,res:null,bld:null,fire:null,smoke:null,
  cost:null,block:null,depth:null,
  nodes:[],buildings:[],cols:[],items:[],enemies:[],animals:[],particles:[],floats:[],jobs:[],
  nid:1,bid:1,cid:1,eid:1,aid:1,
  stock:{wood:0,stone:0,food:0,cloth:0,tools:0,flour:0,bread:0,coin:0},
  cap:{wood:200,stone:200,food:200,cloth:120,tools:60,flour:120,bread:120,coin:1e9},
  flow:{wood:0,stone:0,food:0,cloth:0,tools:0},
  t:{min:6*60,day:0,year:1,speed:1,paused:false,elapsed:0},
  season:0, seasonDay:0, temp:12,
  wx:{type:"clear",t:0,next:2,lightning:0},
  sel:null, tool:null, hoverTile:null, mouse:{x:0,y:0,down:false,drag:null,rdown:false},
  cam:{x:0,y:0,z:1,tx:0,ty:0,tz:1,vx:0,vy:0},
  stats:{built:0,chopped:0,harvested:0,traded:0,killed:0,died:0,daysSurvived:0,waves:0,contracts:0},
  prices:{}, market:{next:4,goods:[]}, buff:{festival:0},
  threat:0, popPeak:0, name:"Colônia", over:false, started:false,
  storageUsed:0, storageCap:0, housingCap:4, militia:[], arms:0,
  mode:"livre", prestige:0, prestigeEarned:0, unlocked:{},
  obj:{active:null, chain:0, done:0, failed:0, cooldown:0, history:[]},
};

function genWorld(seed){
  G.seed=seed; G.rng=new RNG(seed);
  const H=hashStr(String(seed));
  const pn=new Perlin(H), pn2=new Perlin(H^0x9e3779b9), pn3=new Perlin((H*2654435761)>>>0);

  const elev=new Float32Array(MAP_W*MAP_H);
  const moist=new Float32Array(MAP_W*MAP_H);
  const cx=(MAP_W-1)/2, cy=(MAP_H-1)/2, R=max(MAP_W,MAP_H)*0.5;

  for(let y=0;y<MAP_H;y++)for(let x=0;x<MAP_W;x++){
    const i=y*MAP_W+x;
    const nx=x/MAP_W, ny=y/MAP_H;
    // base rolling terrain
    let e=pn.fbm(nx*4.2+11, ny*4.2-7, 5)*0.5+0.5;
    // mountain ridges pushed toward the borders
    const d=Math.hypot(x-cx,y-cy)/R;
    const ridge=pn3.ridged(nx*3.1-30, ny*3.1+14, 5);
    const rim=smooth(sat((d-0.42)/0.62));
    e=e*(1-0.55*rim)+ridge*rim*1.25;
    // a broad gentle valley in the middle
    e+=0.10*(1-smooth(sat(d/0.75)));
    // fine detail
    e+=pn2.noise2(nx*22, ny*22)*0.035;
    elev[i]=e;
    let m=pn2.fbm(nx*3.4-40, ny*3.4+25, 4)*0.5+0.5;
    m+=pn.noise2(nx*9+5, ny*9-3)*0.12;
    moist[i]=sat(m);
  }

  // percentile thresholds → the biome mix stays good for any noise amplitude
  const sorted=Float32Array.from(elev).sort();
  const eq=p=>sorted[clamp(floor(sorted.length*p),0,sorted.length-1)];
  const wl=eq(0.115), deepTop=eq(0.055), sandTop=eq(0.145),
        rockLo=eq(0.80), peakLo=eq(0.905), meadowHi=eq(0.34), treeHi=eq(0.60);

  const msort=Float32Array.from(moist).sort();
  const mq=p=>msort[clamp(floor(msort.length*p),0,msort.length-1)];
  const mDry=mq(0.14), mGrass=mq(0.38), mForest=mq(0.68);

  const bio=new Uint8Array(MAP_W*MAP_H), hgt=new Uint8Array(MAP_W*MAP_H);
  const moi=new Uint8Array(MAP_W*MAP_H), fer=new Uint8Array(MAP_W*MAP_H);
  for(let i=0;i<elev.length;i++){
    const e=elev[i], m=sat(moist[i]);
    let b;
    if(e<deepTop) b=B.DEEP;
    else if(e<wl) b=B.WATER;
    else if(e<sandTop) b=B.SAND;
    else if(e>=peakLo) b=B.PEAK;
    else if(e>=rockLo) b=B.ROCK;
    else if(m>=mForest) b=B.FOREST;
    else if(m>=mGrass) b=(e<meadowHi?B.MEADOW:B.GRASS);
    else if(m>=mDry) b=B.GRASS;
    else b=B.DIRT;
    bio[i]=b;
    hgt[i]=clamp(floor(sat((e-wl)/(1.05-wl))*5),0,5);
    moi[i]=clamp(round(sat((m+sat((e-wl)*1.6)*0.15))*255),0,255);
  }

  // rivers: descend from high ground to the sea
  const carve=(sx,sy)=>{
    let x=sx,y=sy,steps=0,prev=-1;
    while(steps++<MAP_W*3){
      const i=y*MAP_W+x;
      if(bio[i]===B.WATER||bio[i]===B.DEEP)break;
      bio[i]=B.WATER; hgt[i]=0;
      // widen
      if(steps%3===0&&x+1<MAP_W)bio[i+1]=bio[i+1]===B.PEAK?bio[i+1]:B.WATER;
      for(let dy=-4;dy<=4;dy++)for(let dx=-4;dx<=4;dx++){
        const xx=x+dx,yy=y+dy; if(!inb(xx,yy))continue;
        const dd=Math.hypot(dx,dy); if(dd>4)continue;
        const j=yy*MAP_W+xx;
        moist[j]=sat(moist[j]+(1-dd/4)*0.45);
        moi[j]=clamp(round(sat(moist[j])*255),0,255);
      }
      // steepest descent with a little wander
      let best=-1,bx=x,by=y,be=1e9;
      for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){
        if(!dx&&!dy)continue;
        const xx=x+dx,yy=y+dy; if(!inb(xx,yy))continue;
        const j=yy*MAP_W+xx;
        const v=elev[j]+((dx*7+dy*13)%3)*0.004;
        if(v<be&&j!==prev){be=v;best=j;bx=xx;by=yy;}
      }
      if(best<0)break;
      prev=i; x=bx; y=by;
    }
  };
  const rr=new RNG(seed^0x51ed);
  for(let a=0;a<4;a++){
    // find a high spring near a border
    let bx=-1,by=-1,bv=-1;
    for(let tries=0;tries<400;tries++){
      const ang=rr.float(0,TAU), rad=R*rr.float(0.55,0.92);
      const x=clamp(round(cx+Math.cos(ang)*rad),2,MAP_W-3);
      const y=clamp(round(cy+Math.sin(ang)*rad),2,MAP_H-3);
      const i=y*MAP_W+x;
      if(elev[i]>bv&&bio[i]!==B.WATER&&bio[i]!==B.DEEP){bv=elev[i];bx=x;by=y;}
    }
    if(bx>=0)carve(bx,by);
  }

  // fertility: moisture + proximity to water
  const waterDist=new Float32Array(MAP_W*MAP_H).fill(99);
  const q=[];
  for(let i=0;i<bio.length;i++)if(bio[i]===B.WATER||bio[i]===B.DEEP)waterDist[i]=0,q.push(i);
  for(let head=0;head<q.length;head++){
    const i=q[head], x=i%MAP_W, y=(i/MAP_W)|0, d=waterDist[i];
    for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){
      if(!dx&&!dy)continue;
      const xx=x+dx,yy=y+dy; if(!inb(xx,yy))continue;
      const j=yy*MAP_W+xx, nd=d+(abs(dx)+abs(dy)===2?1.42:1);
      if(nd<waterDist[j]){waterDist[j]=nd;q.push(j);}
    }
  }
  for(let i=0;i<bio.length;i++){
    const b=bio[i];
    let f=moi[i]/255*0.55;
    const wd=waterDist[i];
    if(wd<8)f+= (1-wd/8)*0.45;
    if(b===B.FOREST)f+=0.18; else if(b===B.MEADOW)f+=0.14; else if(b===B.GRASS)f+=0.06;
    else if(b===B.SAND)f-=0.35; else if(b===B.DIRT)f-=0.1; else if(b===B.ROCK||b===B.PEAK)f-=0.8;
    fer[i]=clamp(round(sat(f)*100),0,100);
  }

  G.bio=bio;G.hgt=hgt;G.moi=moi;G.fer=fer;
  G.ovr=new Uint8Array(MAP_W*MAP_H);
  G.res=new Int32Array(MAP_W*MAP_H);
  G.bld=new Int32Array(MAP_W*MAP_H);
  G.fire=new Float32Array(MAP_W*MAP_H);
  _fireSet.clear();
  G.smoke=new Float32Array(MAP_W*MAP_H);
  G.cost=new Float32Array(MAP_W*MAP_H);
  G.block=new Uint8Array(MAP_W*MAP_H);
  G.nodes=[];G.nodes.length=0;G.nid=1;
  G.buildings=[];G.bid=1;
  recomputeCost();

  /* scatter resource nodes */
  const sr=new RNG(seed^0xbeef);
  const clump=new Perlin((H^0x1234abcd)>>>0);
  for(let y=1;y<MAP_H-1;y++)for(let x=1;x<MAP_W-1;x++){
    const i=y*MAP_W+x, b=bio[i];
    if(!BPASS[b])continue;
    const cn=clump.fbm(x*0.09,y*0.09,3)*0.5+0.5;
    let kind=0,r=0,a=0,z=0;
    if(b===B.FOREST){
      if(sr.next()<0.30+cn*0.55){
        r=sr.next();
        kind=(elev[i]>treeHi||sr.chance(0.22))?N.PINE:(r<0.52?N.OAK:N.BIRCH);
      }
    } else if(b===B.GRASS){
      r=sr.next(); a=0.010+cn*0.028; z=a+0.013+cn*0.022;
      if(r<a)kind=N.OAK; else if(r<z)kind=N.BUSH; else if(r<z+0.007)kind=N.BOULDER;
    } else if(b===B.MEADOW){
      r=sr.next(); a=0.055+cn*0.085; z=a+0.038+cn*0.042;
      if(r<a)kind=N.FLAX; else if(r<z)kind=N.BUSH; else if(r<z+0.014)kind=N.BIRCH;
    } else if(b===B.ROCK){
      r=sr.next(); a=0.19+cn*0.19; z=a+0.045+cn*0.032;
      if(r<a)kind=N.BOULDER; else if(r<z)kind=N.ORE; else if(r<z+0.022)kind=N.DEADTREE;
    } else if(b===B.DIRT){
      r=sr.next();
      if(r<0.030)kind=N.BOULDER;
      else if(r<0.044)kind=N.DEADTREE;
    } else if(b===B.SAND){
      if(sr.next()<0.012)kind=N.BOULDER;
    }
    if(kind)addNode(kind,x,y,sr);
  }
  recomputeCost();
  return {elev,waterDist};
}

function addNode(kind,x,y,rng){
  rng=rng||G.rng||Math.random;
  const d=NODEDEF[kind];
  const id=G.nid++;
  const n={id,kind,x,y,
    amount:d.yield.wood?round(d.yield.wood*0.8+rng.next()*d.yield.wood*0.5):
           d.yield.food?round(d.yield.food*0.8+rng.next()*d.yield.food*0.5):
           d.yield.stone?round(d.yield.stone*0.8+rng.next()*d.yield.stone*0.5):
           round((d.yield.cloth||2)*(0.8+rng.next()*0.5)),
    max:1, marked:false, dead:false, growth:1, seed:rng.next()*1000,
    variant:rng.int?rng.int(0,2):(Math.random()*3|0), scale:0.85+(rng.next?rng.next():Math.random())*0.35};
  n.max=n.amount;
  G.nodes[id]=n;
  G.res[idx(x,y)]=id;
  recomputeCostLocal(x,y);
  return n;
}
function delNode(n){
  if(!n||n.dead)return;
  n.dead=true;
  const i=idx(n.x,n.y);
  if(G.res[i]===n.id)G.res[i]=0;
  if(G.block[i]&&!G.bld[i])G.block[i]=0;
  recomputeCostLocal(n.x,n.y);
  for(const j of G.jobs)if(j.node===n.id)j.dead=true;
}

function tileCost(i){
  if(G.block[i])return 99;
  const c0=BCOST[G.bio[i]];
  if(c0>=99)return 99;
  if(G.ovr[i]===O.ROAD)return 0.5;
  const r=G.res[i];
  if(r){
    const n=G.nodes[r], d=n&&NODEDEF[n.kind];
    // vegetation slows travel but never walls it off — a forest must not seal the colony in
    if(d&&!n.dead&&!n.hidden)return c0+(d.hp?(n.kind===N.BOULDER||n.kind===N.ORE?5:2.6):0.5);
  }
  return c0;
}
function recomputeCost(){
  for(let i=0;i<G.bio.length;i++)G.cost[i]=tileCost(i);
}
function recomputeCostLocal(x,y){
  for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){
    const xx=x+dx,yy=y+dy; if(!inb(xx,yy))continue;
    const i=idx(xx,yy);
    G.cost[i]=tileCost(i);
  }
}

/* find a good starting camp: flat, grassy, near water + forest, away from peaks */
function findCamp(){
  let best=null,bs=-1e9;
  for(let y=10;y<MAP_H-10;y+=2)for(let x=10;x<MAP_W-10;x+=2){
    const i=idx(x,y), b=G.bio[i];
    if(b!==B.GRASS&&b!==B.MEADOW)continue;
    if(G.res[i])continue;
    let s=G.fer[i]*0.6, water=0, trees=0, rocks=0, flat=0, wild=0;
    for(let dy=-7;dy<=7;dy++)for(let dx=-7;dx<=7;dx++){
      const xx=x+dx,yy=y+dy; if(!inb(xx,yy))continue;
      const j=idx(xx,yy), bb=G.bio[j];
      if(bb===B.WATER||bb===B.DEEP)water++;
      if(G.res[j]){const k=G.nodes[G.res[j]].kind;
        if(k===N.OAK||k===N.PINE||k===N.BIRCH)trees++;
        else if(k===N.BOULDER||k===N.ORE)rocks++;
        else if(k===N.BUSH||k===N.FLAX)wild++;}
      if(bb===B.GRASS||bb===B.MEADOW||bb===B.DIRT)flat++;
    }
    if(water<4||trees<22||wild<2)continue;
    s+= water*2.2 + trees*1.1 + rocks*1.6 + flat*0.25 + wild*7;
    s-= Math.abs(water-40)*0.35;
    if(s>bs){bs=s;best={x,y};}
  }
  if(!best)best={x:MAP_W>>1,y:MAP_H>>1};
  return best;
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 4 · pathfinding (A* with binary heap)
═══════════════════════════════════════════════════════════════════════════════*/

const Heap=(()=>{
  function H(){this.a=[];}
  H.prototype.push=function(node){
    const a=this.a; a.push(node);
    let i=a.length-1;
    while(i>0){const p=(i-1)>>1; if(a[p].f<=a[i].f)break; const t=a[p];a[p]=a[i];a[i]=t; i=p;}
  };
  H.prototype.pop=function(){
    const a=this.a, top=a[0], last=a.pop();
    if(a.length){a[0]=last; let i=0;
      for(;;){const l=i*2+1,r=l+1; let s=i;
        if(l<a.length&&a[l].f<a[s].f)s=l;
        if(r<a.length&&a[r].f<a[s].f)s=r;
        if(s===i)break; const t=a[s];a[s]=a[i];a[i]=t; i=s;}}
    return top;
  };
  H.prototype.clear=function(){this.a.length=0;};
  Object.defineProperty(H.prototype,"size",{get:function(){return this.a.length;}});
  return H;
})();

const _gScore=new Float32Array(MAP_W*MAP_H);
const _came=new Int32Array(MAP_W*MAP_H);
const _stamp=new Int32Array(MAP_W*MAP_H);
const _closed=new Uint8Array(MAP_W*MAP_H);
let _stampN=0;
const _heap=new Heap();
const _NB=[[1,0,1],[-1,0,1],[0,1,1],[0,-1,1],[1,1,1.4142],[1,-1,1.4142],[-1,1,1.4142],[-1,-1,1.4142]];

function passable(i){return i>=0&&i<G.cost.length&&G.cost[i]<90;}

/** A* on the tile grid. Returns array of tile indices from start→goal (inclusive) or null. */
function findPath(sx,sy,gx,gy,maxNodes=9000){
  if(!inb(sx,sy)||!inb(gx,gy))return null;
  const si=idx(sx,sy), gi=idx(gx,gy);
  if(si===gi)return [si];
  if(!passable(gi))return null;
  _stampN++;
  const st=_stampN;
  _heap.clear();
  _gScore[si]=0; _came[si]=-1; _stamp[si]=st; _closed[si]=0;
  _heap.push({i:si,f:Math.abs(gx-sx)+Math.abs(gy-sy)});
  let explored=0;
  while(_heap.size){
    const cur=_heap.pop();
    const ci=cur.i;
    if(_stamp[ci]===st&&_closed[ci])continue;
    _closed[ci]=1;
    if(ci===gi){
      // reconstruct
      const out=[]; let c=gi;
      while(c!==-1&&out.length<4000){out.push(c); c=_came[c];}
      out.reverse(); return out;
    }
    if(++explored>maxNodes)break;
    const cx=ci%MAP_W, cy=(ci/MAP_W)|0, cg=_gScore[ci];
    for(let n=0;n<8;n++){
      const nb=_NB[n], nx=cx+nb[0], ny=cy+nb[1];
      if(nx<0||ny<0||nx>=MAP_W||ny>=MAP_H)continue;
      const ni=ny*MAP_W+nx;
      if(G.cost[ni]>=90)continue;
      // forbid corner cutting through blocked diagonals
      if(nb[2]>1&&(G.cost[cy*MAP_W+nx]>=90||G.cost[ny*MAP_W+cx]>=90))continue;
      const ng=cg+nb[2]*G.cost[ni];
      if(_stamp[ni]!==st||ng<_gScore[ni]){
        _gScore[ni]=ng;_came[ni]=ci;_stamp[ni]=st;_closed[ni]=0;
        const h=(Math.abs(gx-nx)+Math.abs(gy-ny))*1.02;
        _heap.push({i:ni,f:ng+h});
      }
    }
  }
  return null;
}

/** nearest walkable tile adjacent to (or at) target */
function adjTargets(tx,ty,w,h){
  const out=[];
  for(let y=ty-1;y<=ty+h;y++)for(let x=tx-1;x<=tx+w;x++){
    const inside=x>=tx&&x<tx+w&&y>=ty&&y<ty+h;
    if(inside)continue;
    if(!inb(x,y))continue;
    if(G.cost[idx(x,y)]<90)out.push({x,y});
  }
  return out;
}
const _goalS=new Int32Array(MAP_W*MAP_H);
function rectDist(x,y,tx,ty,w,h){
  const dx=Math.abs(x-(tx+(w-1)/2))-(w-1)/2;
  const dy=Math.abs(y-(ty+(h-1)/2))-(h-1)/2;
  return (dx>0?dx:0)+(dy>0?dy:0);
}
/** Path to the nearest walkable tile touching a multi-tile footprint.
    Runs a single A* whose goal set is every candidate tile — searching each
    candidate separately made idle colonists cost ~12 full map scans per tick. */
function pathToArea(sx,sy,tx,ty,w=1,h=1){
  if(!inb(sx,sy))return null;
  const cands=adjTargets(tx,ty,w,h);
  if(!cands.length)return null;
  const si=idx(sx,sy);
  if(_region&&_homeRegion&&_region[si]){
    if(_region[si]!==_homeRegion)return null;
    let reach=false;
    for(const c of cands){ if(_region[idx(c.x,c.y)]===_homeRegion){reach=true;break;} }
    if(!reach)return null;
  }
  if(cands.length===1)return findPath(sx,sy,cands[0].x,cands[0].y);
  _stampN++; const st=_stampN;
  for(const c of cands)_goalS[idx(c.x,c.y)]=st;
  _heap.clear();
  _gScore[si]=0;_came[si]=-1;_stamp[si]=st;_closed[si]=0;
  _heap.push({i:si,f:rectDist(sx,sy,tx,ty,w,h)});
  let explored=0;
  while(_heap.size){
    const cur=_heap.pop(); const ci=cur.i;
    if(_stamp[ci]===st&&_closed[ci])continue;
    _closed[ci]=1;
    if(_goalS[ci]===st){
      const out=[]; let c=ci;
      while(c!==-1&&out.length<4000){out.push(c); c=_came[c];}
      out.reverse(); return out;
    }
    if(++explored>9000)break;
    const cx=ci%MAP_W, cy=(ci/MAP_W)|0, cg=_gScore[ci];
    for(let n=0;n<8;n++){
      const nb=_NB[n], nx=cx+nb[0], ny=cy+nb[1];
      if(nx<0||ny<0||nx>=MAP_W||ny>=MAP_H)continue;
      const ni=ny*MAP_W+nx;
      if(G.cost[ni]>=90)continue;
      if(nb[2]>1&&(G.cost[cy*MAP_W+nx]>=90||G.cost[ny*MAP_W+cx]>=90))continue;
      const ng=cg+nb[2]*G.cost[ni];
      if(_stamp[ni]!==st||ng<_gScore[ni]){
        _gScore[ni]=ng;_came[ni]=ci;_stamp[ni]=st;_closed[ni]=0;
        _heap.push({i:ni,f:ng+rectDist(nx,ny,tx,ty,w,h)*1.02});
      }
    }
  }
  return null;
}
/* Connectivity: label every walkable tile with its flood-fill region, so placement
   can reject plots the colony can never walk to and the job AI can skip work across
   a river instead of re-running A* every cooldown. */
let _region=null,_regQ=null,_homeRegion=0,_homeSize=0;
function rebuildRegions(){
  const N=MAP_W*MAP_H;
  if(!_region||_region.length!==N){_region=new Int32Array(N);_regQ=new Int32Array(N);}
  _region.fill(0);
  let id=0;
  for(let s=0;s<N;s++){
    if(_region[s]||G.cost[s]>=90)continue;
    id++;
    let h=0,t=0; _regQ[t++]=s; _region[s]=id;
    while(h<t){
      const i=_regQ[h++], x=i%MAP_W, y=(i/MAP_W)|0;
      if(x>0){const j=i-1;      if(!_region[j]&&G.cost[j]<90){_region[j]=id;_regQ[t++]=j;}}
      if(x<MAP_W-1){const j=i+1;if(!_region[j]&&G.cost[j]<90){_region[j]=id;_regQ[t++]=j;}}
      if(y>0){const j=i-MAP_W;  if(!_region[j]&&G.cost[j]<90){_region[j]=id;_regQ[t++]=j;}}
      if(y<MAP_H-1){const j=i+MAP_W;if(!_region[j]&&G.cost[j]<90){_region[j]=id;_regQ[t++]=j;}}
    }
  }
  _homeRegion=0;
  if(G.camp){
    // the camp spot itself can legitimately be paved over by a building, so take the
    // nearest walkable tile around it as the home anchor
    const cx=G.camp.x|0, cy=G.camp.y|0;
    for(let r=0;r<=6&&!_homeRegion;r++){
      for(let dy=-r;dy<=r&&!_homeRegion;dy++)for(let dx=-r;dx<=r&&!_homeRegion;dx++){
        if(r>0&&Math.abs(dx)!==r&&Math.abs(dy)!==r)continue;
        const x=cx+dx,y=cy+dy; if(!inb(x,y))continue;
        const v=_region[idx(x,y)]; if(v)_homeRegion=v;
      }
    }
  }
  _homeSize=0;
  if(_homeRegion)for(let i=0;i<N;i++)if(_region[i]===_homeRegion)_homeSize++;
}
function inHomeRegion(x,y){
  if(!_region||!_homeRegion)return true;
  const i=idx(x|0,y|0);
  return i>=0&&i<_region.length&&_region[i]===_homeRegion;
}
function hasHomeAccess(x,y,w,h){
  if(!_region||!_homeRegion)return true;
  for(let j=y-1;j<=y+h;j++)for(let i=x-1;i<=x+w;i++){
    if(!inb(i,j))continue;
    if(_region[idx(i,j)]===_homeRegion)return true;
  }
  return false;
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 5 · buildings, jobs, items, farms, crafting, fire
═══════════════════════════════════════════════════════════════════════════════*/

function storageCap(){let c=260;for(const b of G.buildings)if(b&&!b.dead&&b.built>=1&&BDEF[b.def].store)c+=BDEF[b.def].store;return c;}
function stockTotal(){return G.stock.wood+G.stock.stone+G.stock.food+G.stock.cloth+G.stock.tools+G.stock.flour+G.stock.bread;}
function canAfford(cost){for(const k in cost)if((G.stock[k]|0)<cost[k])return false;return true;}
function pay(cost){for(const k in cost)G.stock[k]-=cost[k];}
function addStock(k,n){
  if(k==="coin"){G.stock.coin+=n;return n;}
  const cap=storageCap(), free=cap-stockTotal();
  const put=Math.max(0,Math.min(n,free));
  G.stock[k]+=put;
  return put;
}
function housingCap(){let c=0;for(const b of G.buildings)if(b&&!b.dead&&b.built>=1&&BDEF[b.def].beds)c+=BDEF[b.def].beds;return c;}
function edible(){return G.stock.food+G.stock.bread;}
function takeMeal(c){
  if(G.stock.bread>0){
    G.stock.bread--;
    c.hunger=min(100,c.hunger+86);
    c.mood=min(100,c.mood+5);c.warm=min(100,c.warm+7);
    if(chance(.3))c.energy=min(100,c.energy+6);
    return true;
  }
  if(G.stock.food>0){G.stock.food--;c.hunger=min(100,c.hunger+62);}
  return false;
}

let _dropCache=null;
function dropPoints(){
  if(_dropCache)return _dropCache;
  const out=[];
  for(const b of G.buildings){
    if(!b||b.dead||b.built<1)continue;
    if(BDEF[b.def].store){
      for(const t of adjTargets(b.x,b.y,b.w,b.h))out.push({x:t.x,y:t.y,b});
    }
  }
  if(G.camp)out.push({x:G.camp.x,y:G.camp.y,b:null});
  _dropCache=out.length?out:null;
  return _dropCache;
}
function invalidateDrop(){_dropCache=null;}

/* ── placement validation ─────────────────────────────────────────────── */
function isCampTile(x,y){
  if(!G.camp)return false;
  const b=G.campBld||{x:G.camp.x,y:G.camp.y,w:2,h:2};
  return x>=b.x&&x<b.x+(b.w||2)&&y>=b.y&&y<b.y+(b.h||2);
}
function canPlace(key,x,y){
  const d=BDEF[key]; if(!d)return {ok:false,why:"—"};
  if(x<0||y<0||x+d.w>MAP_W||y+d.h>MAP_H)return{ok:false,why:"Fora do mapa"};
  if(!isUnlocked(key))return{ok:false,why:"Bloqueado — gaste prestígio (tecla O)"};
  let rockNear=0,waterNear=0,land=0;
  for(let j=y-1;j<=y+d.h;j++)for(let i=x-1;i<=x+d.w;i++){
    if(i<x||i>=x+d.w||j<y||j>=y+d.h){
      if(inb(i,j)){const b=G.bio[idx(i,j)];if(b===B.ROCK||b===B.PEAK)rockNear++;
        if(b===B.WATER||b===B.DEEP)waterNear++;}
      continue;
    }
    if(!inb(i,j))return{ok:false,why:"Fora do mapa"};
    if(isCampTile(i,j))return{ok:false,why:"Não se constrói sobre o acampamento"};
    const ii=idx(i,j), b=G.bio[ii];
    if(!BPASS[b])return{ok:false,why:"Precisa de terra firme"};
    if(G.res[ii])return{ok:false,why:"Vegetação/rocha no caminho — use Demolir"};
    if(G.bld[ii])return{ok:false,why:"Já existe construção"};
    if(d.soil){
      if(b!==B.GRASS&&b!==B.MEADOW&&b!==B.DIRT)return{ok:false,why:"Solo inadequado"};
      if(G.fer[ii]<22)return{ok:false,why:"Solo pobre (fertilidade < 22)"};
    }
    land++;
  }
  if(d.near==="rock"&&rockNear<2)return{ok:false,why:"Precisa de rochedo adjacente"};
  if(d.near==="water"&&waterNear<1)return{ok:false,why:"Precisa de água correndo por perto"};
  if(!canAfford(d.cost))return{ok:false,why:"Recursos insuficientes"};
  if(!hasHomeAccess(x,y,d.w,d.h))return{ok:false,why:"Sem caminho a partir da colônia"};
  return {ok:true,land};
}

function placeBuilding(key,x,y,free){
  const d=BDEF[key];
  const chk=free?{ok:true}:canPlace(key,x,y);
  if(!chk.ok){Audio_.err();return null;}
  if(!free)pay(d.cost);
  const id=G.bid++;
  const b={id,def:key,x,y,w:d.w,h:d.h,hp:d.hp,maxhp:d.hp,built:free?1:0,dead:false,
    work:0,workNeed:0,mats:{},crop:null,growth:0,tilled:false,stage:0,queue:[],
    quality:0,mineT:0,orchT:0,taxT:0,fire:0,seed:Math.random()*1000,anim:0,
    militia:[],lit:d.light||0,flags:{}};
  if(d.store)b.store=0;
  if(key==="farm")b.crop="wheat";
  for(const k in d.cost)b.mats[k]=d.cost[k];
  b.workNeed=Math.max(3,Object.values(d.cost).reduce((a,c)=>a+c,0)*0.42);
  G.buildings[id]=b;
  for(let j=y;j<y+d.h;j++)for(let i=x;i<x+d.w;i++){
    const ii=idx(i,j);
    G.bld[ii]=id;
    if(d.ovr)G.ovr[ii]=d.ovr;
    if(!d.ovr||d.block)G.block[ii]=1;
  }
  if(free){b.built=1;b.work=b.workNeed;}
  else addJob({type:"build",x,y,bx:id,prio:10,work:b.workNeed,skill:"build"});
  recomputeCost(); invalidateDrop(); rebuildRegions(); G.stats.built++;
  Audio_.build();
  return b;
}

function demolish(b,silent){
  if(!b||b.dead)return;
  b.dead=true;
  const d=BDEF[b.def];
  for(let j=b.y;j<b.y+b.h;j++)for(let i=b.x;i<b.x+b.w;i++){
    const ii=idx(i,j);
    if(G.bld[ii]===b.id){G.bld[ii]=0;G.block[ii]=0;if(d.ovr)G.ovr[ii]=O.NONE;}
    G.fire[ii]=0;_fireSet.delete(ii);
  }
  for(const j of G.jobs)if(j.bx===b.id)j.dead=true;
  if(!silent){
    const refund={};
    for(const k in b.mats)refund[k]=Math.floor(b.mats[k]*(b.built>=1?0.5:0.9));
    let any=false;
    for(const k in refund){if(refund[k]>0){addStock(k,refund[k]);any=true;}}
    if(any)notify("Demolição","Materiais recuperados.","info");
    for(let i=0;i<14;i++)spawnParticle(b.x+.5,b.y+.5,"dust");
  }
  recomputeCost(); invalidateDrop(); rebuildRegions();
}

/* ── ground items ─────────────────────────────────────────────────────── */
const ITEM_LIFE=7*DT_DAY;   // a stack left on the ground spoils after ~7 game days
function dropItem(kind,amount,x,y,noJob){
  if(amount<=0)return;
  for(const it of G.items){
    if(!it.dead&&it.kind===kind&&it.x===x&&it.y===y){it.amount+=amount;it.pop=1;it.life=ITEM_LIFE;
      if(!noJob&&!G.jobs.some(j=>!j.dead&&j.item===it.id))addJob({type:"haul",x,y,item:it.id,prio:5,skill:null});
      return it;}
  }
  const it={id:G.nid++,kind,amount,x,y,dead:false,bob:Math.random()*TAU,pop:1,vy:0,life:ITEM_LIFE};
  G.items.push(it);
  if(!noJob)addJob({type:"haul",x,y,item:it.id,prio:5,skill:null});
  return it;
}
function killItem(it){
  it.dead=true; it.amount=0; if(it.taken)it.taken=0;
  killJobsFor(j=>j.item===it.id);
}
function itemAging(dt){
  for(const it of G.items){
    if(it.dead)continue;
    if(it.life===undefined)it.life=ITEM_LIFE;   // saves written before spoiling existed
    it.life-=dt;
    if(it.life<=0)killItem(it);
  }
  // hard ceiling: an unbounded pile makes every drop/haul/render scan quadratic and freezes the game
  if(G.items.length>420){
    G.items.sort((a,b)=>a.life-b.life);
    const cut=G.items.length-420;
    for(let i=0;i<cut;i++)if(!G.items[i].dead)killItem(G.items[i]);
    G.items=G.items.filter(i=>!i.dead);
  }
}
function giveYield(yields,x,y,skillMul){
  for(const k in yields){
    let n=yields[k];
    if(k!=="coin")n=Math.max(1,Math.round(n*(skillMul||1)));
    if(k==="coin"){G.stock.coin+=n;spawnFloat(x,y,"+"+n+" moedas","#e0a145");}
    else dropItem(k,n,x,y);
  }
}

/* ── jobs ─────────────────────────────────────────────────────────────── */
function addJob(j){
  j.id=G.nid++; j.dead=false; j.by=0; j.prog=0;
  G.jobs.push(j);
  return j;
}
function killJobsFor(pred){for(const j of G.jobs)if(!j.dead&&pred(j))j.dead=true;}
function jobAt(x,y,type){return G.jobs.find(j=>!j.dead&&j.by===0&&j.x===x&&j.y===y&&(!type||j.type===type));}

const SKILL_OF={chop:"forestry",mine:"mining",gather:"farming",haul:null,build:"construction",
  till:"farming",sow:"farming",harvest:"farming",craft:"crafting",water:null,heal:"medicine",
  clear:null,defend:"fighting",brew:"crafting"};

function scoreJob(c,j){
  if(j.dead||j.by)return -1e9;
  if(j.coolU&&j.coolU>G.t.min)return -1e9;
  // never burn A* on work the colony physically cannot reach
  if(!inHomeRegion(j.x,j.y))return -1e9;
  // with no shelf space, hauling is busywork: goods would just be carried back out again
  if(j.type==="haul"&&!c.carry&&stockTotal()>=storageCap())return -1e9;
  const sk=SKILL_OF[j.type];
  let s=j.prio*14;
  const d=Math.hypot(j.x-c.x,j.y-c.y);
  s-=d*0.55;
  if(sk)s+=(c.skill[sk]||0)*1.6;
  else s+=6;
  // preference: colonists avoid jobs across deep water
  if(j.type==="haul"&&c.carry)s-=30;
  if(c.traits.includes("medr")&&(j.type==="defend"))return -1e9;
  if(j.type==="defend"&&!c.militia&&!c.traits.includes("brav"))s-=60;
  return s;
}

function bestJob(c){
  let bj=null,bs=-1e8;
  for(const j of G.jobs){
    if(j.dead||j.by===c.id)continue;
    if(j.by&&j.by!==c.id){
      // allow stealing if the reserver is far and the job is urgent
      if(j.prio<15)continue;
    }
    const s=scoreJob(c,j);
    if(s>bs){bs=s;bj=j;}
  }
  return bj;
}

/* ── farms ────────────────────────────────────────────────────────────── */
function farmTick(b,dt){
  const d=BDEF[b.def];
  const gdt=dt/DT_DAY;
  if(b.def==="orchard"){
    if(b.built<1)return;
    b.orchT+=gdt;
    if(b.maturity===undefined)b.maturity=0.05;
    if(G.season!==3)b.maturity=min(1,b.maturity+gdt/44);
    if(G.season===2&&b.orchT>4){
      b.orchT=0;
      const y=3+round(b.maturity*9);
      dropItem("food",y,b.x,b.y);
      spawnFloat(b.x+.5,b.y,"+"+y+" comida","#e8c25a");
    }
    return;
  }
  if(b.built<1)return;
  const S=G.season;
  if(b.crop&&b.tilled&&b.stage>0&&b.stage<4){
    const cd=CROPS[b.crop];
    let rate=gdt*SEASONS[S].grow*WEATHER[G.wx.type].grow*(0.55+G.fer[idx(b.x+1,b.y+1)]/100*0.75);
    if(G.wx.type==="rain")rate*=1.1;
    b.growth+=rate/cd.grow;
    if(b.growth>=1){b.growth=1;b.stage=4;
      if(!jobAt(b.x,b.y,"harvest"))addJob({type:"harvest",x:b.x,y:b.y,bx:b.id,prio:9,work:2.6,skill:"farming"});
    } else {
      const st=1+floor(b.growth*3);
      if(st!==b.stage){b.stage=st;}
    }
  }
  // seasonal automation
  if(S===0){
    if(!b.tilled&&!jobAt(b.x,b.y,"till"))addJob({type:"till",x:b.x,y:b.y,bx:b.id,prio:6,work:3,skill:"farming"});
    else if(b.tilled&&b.stage===0&&!jobAt(b.x,b.y,"sow")&&(CROPS[b.crop].plant===0))
      addJob({type:"sow",x:b.x,y:b.y,bx:b.id,prio:6,work:1.6,skill:"farming"});
  } else if(S===1){
    if(b.tilled&&b.stage===0&&CROPS[b.crop].plant===1&&!jobAt(b.x,b.y,"sow"))
      addJob({type:"sow",x:b.x,y:b.y,bx:b.id,prio:6,work:1.6,skill:"farming"});
  } else if(S===2){
    if(b.tilled&&b.stage===0&&CROPS[b.crop].plant===2&&!jobAt(b.x,b.y,"sow"))
      addJob({type:"sow",x:b.x,y:b.y,bx:b.id,prio:7,work:1.6,skill:"farming"});
  } else {
    // winter: fields freeze; clear them for next year
    if(b.stage>0&&b.stage<4&&b.growth<0.85){
      b.stage=0;b.growth=0;b.tilled=false;
      killJobsFor(j=>j.bx===b.id&&(j.type==="sow"||j.type==="till"||j.type==="harvest"));
    }
    if(b.stage===4&&!jobAt(b.x,b.y,"harvest"))
      addJob({type:"harvest",x:b.x,y:b.y,bx:b.id,prio:9,work:2.6,skill:"farming"});
  }
}

/* ── crafting ─────────────────────────────────────────────────────────── */
function craftTick(b,dt){
  if(b.built<1)return;
  // the mill turns and the oven stays hot on their own — but never at the cost of the larder
  if(!b.queue.length&&(b.def==="mill"||b.def==="bakery")){
    const pop=max(1,aliveCols().length);
    if(b.def==="mill"&&G.stock.food>pop*4+16&&G.stock.flour<90)b.queue.push({r:"flour"});
    else if(b.def==="bakery"&&G.stock.flour>=6&&G.stock.bread<60)b.queue.push({r:"bread"});
  }
  if(b.queue.length&&stockTotal()>0){
    const q=b.queue[0];
    if(!jobAt(b.x,b.y,"craft")&&canAfford(RECIPES[q.r].in))
      addJob({type:"craft",x:b.x,y:b.y,bx:b.id,prio:7,work:RECIPES[q.r].time,skill:"crafting",recipe:q.r,qi:0});
  }
  // mines produce stone continuously
  if(b.def==="mine"){
    b.mineT+=dt;
    if(b.mineT>0.35*DT_DAY){
      b.mineT=0;
      if(!jobAt(b.x,b.y,"mine2"))
        addJob({type:"mine2",x:b.x,y:b.y,bx:b.id,prio:5,work:5,skill:"mining"});
    }
  }
  // markets levy taxes
  if(b.def==="market"&&G.cols.length){
    b.taxT+=dt;
    if(b.taxT>DT_DAY){
      b.taxT=0;
      const g=1+Math.round(avgMood()/28)+Math.round(G.cols.length*0.35);
      G.stock.coin+=g;
      spawnFloat(b.x+.5,b.y,"+"+g+" moedas","#e0a145");
    }
  }
}

/* ── prestige buildings: lessons and drills ───────────────────────────── */
function academyOn(){for(const b of G.buildings)if(b&&!b.dead&&b.built>=1&&b.def==="academy")return true;return false;}
function garrisonOn(){for(const b of G.buildings)if(b&&!b.dead&&b.built>=1&&b.def==="garrison")return true;return false;}
function schoolTick(b,dt){
  b.taxT=(b.taxT||0)+dt;
  if(b.taxT<DT_DAY*0.5)return;
  b.taxT=0;
  if(b.def==="academy"){
    const cols=aliveCols().filter(c=>c.state==="idle"||c.age<18);
    if(!cols.length)return;
    const c=pick(cols);
    gainXP(c,pick(Object.keys(SKNAME)),16);
    spawnFloat(c.x,c.y,"na escola","#9fd0ff");
  } else {
    const m=aliveCols().filter(c=>c.militia);
    if(!m.length)return;
    const c=pick(m);
    gainXP(c,"fighting",14);
    spawnFloat(c.x,c.y,"treino","#ffb27a");
  }
}

/* ── fire ─────────────────────────────────────────────────────────────── */
const FIRE_DRY=[0.8,1.35,1.0,0.4];   // spring · summer · autumn · winter
const _fireSet=new Set(); let _fireList=[];
function rebuildFireSet(){
  _fireSet.clear();
  for(let i=0;i<G.fire.length;i++)if(G.fire[i]>0)_fireSet.add(i);
}
function ignite(x,y,amt){
  if(!inb(x,y))return;
  const i=idx(x,y);
  const b=G.bio[i];
  if(b===B.WATER||b===B.DEEP)return;
  // Float32Array rounds, so never compare the stored value back to `amt` to detect
  // a fresh ignition — test the tile before writing it or no firefighter is ever called
  const fresh=!(G.fire[i]>0);
  G.fire[i]=min(1.4,(G.fire[i]||0)+amt);
  _fireSet.add(i);
  if(fresh&&!jobAt(x,y,"water")){
    addJob({type:"water",x,y,prio:22,work:2,skill:null});
    if(!G._fireOn&&G.started){G._fireOn=true;notify("Incêndio!","Focos de fogo se espalhando — os colonos vão combater.","bad");}
  }
}
function fireTick(dt){
  if(!_fireSet.size){G._fireOn=false;return false;}
  const wt=G.wx.type;
  const wet=(wt==="rain"||wt==="storm")?0.55:(wt==="snow"?0.4:0);
  // season dryness: summer fires run away, winter ones sputter out
  const dry=FIRE_DRY[clamp(G.season|0,0,3)]*(wet?0.25:1);
  _fireList.length=0; for(const i of _fireSet)_fireList.push(i);
  for(let q=0;q<_fireList.length;q++){
    const i=_fireList[q];
    let f=G.fire[i];
    if(!(f>0)){_fireSet.delete(i);continue;}
    const x=i%MAP_W,y=(i/MAP_W)|0;
    f-=dt*(0.0042+wet*0.05);
    // spread: a strong flame reaches for one adjacent tile at a time
    if(f>0.3&&chance(dt*0.02*dry)){
      const dx=randInt(-1,1),dy=randInt(-1,1);
      if((dx||dy)&&inb(x+dx,y+dy)){
        const j=idx(x+dx,y+dy);
        const fuel=fuelAt(j);
        if(fuel>0&&G.fire[j]<0.2)ignite(x+dx,y+dy,0.55*fuel+0.3);
      }
    }
    // damage
    const bid=G.bld[i];
    if(bid){const b=G.buildings[bid];if(b&&!b.dead){b.hp-=dt*f*0.6;if(b.hp<=0)destroyBuilding(b,"incêndio");}}
    const nid=G.res[i];
    if(nid){const n=G.nodes[nid];if(n&&!n.dead){n.amount-=dt*f*0.08;if(n.amount<=0){delNode(n);}}}
    if(f<=0){G.fire[i]=0;_fireSet.delete(i);killJobsFor(j=>j.type==="water"&&j.x===x&&j.y===y);}
    else G.fire[i]=f;
    if(chance(dt*9))spawnParticle(x+.5+rand(-.3,.3),y+.5,"fire");
    if(chance(dt*5))spawnParticle(x+.5+rand(-.2,.2),y+.4,"smoke");
  }
  if(!_fireSet.size)G._fireOn=false;
  return _fireSet.size>0;
}
function fuelAt(i){
  const nid=G.res[i];
  if(nid){const n=G.nodes[nid];if(n&&!n.dead&&NODEDEF[n.kind].sway>0)return 1;}
  const bid=G.bld[i];
  if(bid){const b=G.buildings[bid];if(b&&!b.dead)return BDEF[b.def].cost.wood?0.9:0.25;}
  const bb=G.bio[i];
  if(bb===B.FOREST)return 0.5; if(bb===B.GRASS||bb===B.MEADOW)return 0.22;
  return 0;
}
function destroyBuilding(b,cause){
  notify("Construção perdida", BDEF[b.def].name+" destruída por "+cause+".","bad");
  for(let i=0;i<20;i++)spawnParticle(b.x+rand(0,b.w),b.y+rand(0,b.h),"dust");
  demolish(b,true);
  Audio_.doom();
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 6 · colonists: needs, skills, AI · fauna · raiders · combat
═══════════════════════════════════════════════════════════════════════════════*/

const SKILLS=["forestry","mining","farming","construction","crafting","medicine","fighting"];
const SKNAME={forestry:"Silvicultura",mining:"Mineração",farming:"Agricultura",construction:"Construção",crafting:"Artesanato",medicine:"Medicina",fighting:"Combate"};
const SKILL_LV=x=>min(20,floor(Math.sqrt(max(0,x)/5)));

const SKIN=[[238,196,160],[224,172,130],[196,140,98],[158,104,68],[112,72,48],[246,214,186]];
const HAIR=[[42,30,22],[86,54,30],[146,96,44],[198,166,96],[222,222,228],[28,26,30],[122,52,38]];
const CLOTH_C=[[86,110,152],[142,74,72],[72,116,92],[126,96,142],[168,132,66],[64,84,104],[142,110,88]];

function makeColonist(x,y,veteran){
  const rng=G.rng||new RNG(Date.now());
  const sex=chance(.5)?"m":"f";
  const first=sex==="m"?pick(NAMES_M):pick(NAMES_F);
  const id=G.cid++;
  const traits=[];
  const nt=veteran?1:rng.int(1,2);
  while(traits.length<nt){const t=pick(TRAIT);if(!traits.includes(t.id))traits.push(t.id);}
  const c={
    id, name:first+" "+pick(SURNAMES), first, sex, age:rng.int(18,54),
    x:x+.5, y:y+.5, tx:x, ty:y, dir:0, walk:0, moving:false,
    path:null, pi:0, dest:null,
    speed:1.85+rng.float(-.16,.2),
    hunger:100-rng.float(0,25), energy:100-rng.float(0,20), mood:62+rng.float(-8,8), health:100,
    warm:100, hygiene:80,
    skill:{}, xp:{},
    traits, carry:null, job:null, phase:"", workT:0, seekT:rng.float(0,.5),
    state:"idle", stateTxt:"Ocioso", target:null, attackT:0, militia:false, tower:null,
    tool:false, clothes:false, bed:null, home:null, sleepGround:0, idleT:0, breakT:0,
    skin:pick(SKIN), hair:pick(HAIR), cloth:pick(CLOTH_C), hairStyle:rng.int(0,3),
    alive:true, bornDay:G.t.day, kills:0, built:0, harvested:0, thought:"", thoughtT:0,
    speedMul:1, lastHomeless:0,
  };
  for(const s of SKILLS){c.xp[s]=0;c.skill[s]=0;}
  if(veteran){const s=pick(SKILLS);c.xp[s]=rng.float(60,160);c.skill[s]=SKILL_LV(c.xp[s]);}
  // starting kit
  if(rng.chance(.35))c.tool=G.stock.tools>0;
  G.cols[id]=c;
  return c;
}
function killColonist(c,cause){
  if(!c.alive)return;
  c.alive=false; c.dead=true;
  if(c.job){c.job.by=0;c.job=null;}
  G.stats.died++;
  G.moodShock=14;
  for(let i=0;i<18;i++)spawnParticle(c.x,c.y,"blood");
  spawnFloat(c.x,c.y,c.first+" morreu","#f0685a");
  notify("Morte na colônia", c.name+" morreu ("+cause+").","bad");
  Audio_.death();
}
function aliveCols(){return G.cols.filter(c=>c&&c.alive);}
function avgMood(){const a=aliveCols();return a.length?a.reduce((s,c)=>s+c.mood,0)/a.length:0;}
function avgHealth(){const a=aliveCols();return a.length?a.reduce((s,c)=>s+c.health,0)/a.length:0;}

function gainXP(c,sk,amt){
  if(!sk)return;
  c.xp[sk]+=amt*(academyOn()?1.35:1);
  const lv=SKILL_LV(c.xp[sk]);
  if(lv>c.skill[sk]){
    c.skill[sk]=lv;
    spawnFloat(c.x,c.y-0.4,SKNAME[sk]+" "+lv,"#7fd0ff");
    Audio_.levelup();
    if(lv%5===0)notify("Habilidade aprimorada",c.first+" atingiu "+SKNAME[sk]+" "+lv+".","good");
  }
}
function workSpeed(c){
  let s=1;
  s*=1+(c.skill[SKILL_OF[c.job?.type]||"forestry"]||0)*0.055;
  if(c.tool)s*=1.3;
  s*=0.66+c.mood/100*0.5;
  if(c.traits.includes("trab"))s*=1.2;
  if(c.traits.includes("lent"))s*=0.8;
  if(c.traits.includes("notu")&&isNight())s*=1.2;
  if(G.buff.festival>0)s*=1.08;
  s*=WEATHER[G.wx.type].speed*0.35+0.65;
  if(c.health<60)s*=0.6+c.health/150;
  return s;
}
function carryCap(c){return c.traits.includes("fort")?14:10;}

/* ── movement ─────────────────────────────────────────────────────────── */
function setPath(c,p){
  c.path=p;c.pi=p?1:0;c.moving=!!p;
  if(p&&p.length>1){const t=p[0];c.x=t%MAP_W+.5;c.y=((t/MAP_W)|0)+.5;}
}
function moveTo(c,x,y){
  const p=findPath(c.tx,c.ty,x,y);
  if(!p){const q=pathToArea(c.tx,c.ty,x,y,1,1);setPath(c,q);return !!q;}
  setPath(c,p);return true;
}
function moveAlong(c,dt){
  if(!c.path||c.pi>=c.path.length){c.moving=false;return true;}
  const ti=c.path[c.pi], tx=ti%MAP_W, ty=(ti/MAP_W)|0;
  const cx=tx+.5, cy=ty+.5;
  const dx=cx-c.x, dy=cy-c.y, d=Math.hypot(dx,dy)||1e-6;
  let cost=G.cost[ti]; if(cost>=90)cost=1.6;
  const sp=c.speed*c.speedMul*(1/cost)*dt;
  c.dir=Math.atan2(dy,dx);
  if(d<=sp){
    c.x=cx;c.y=cy;c.pi++;c.tx=tx;c.ty=ty;
    // flat per-tile burn: this fires on arrival at a segment, not continuously,
    // so scaling it by dt would kill a colonist outright at high game speed
    if(G.fire[ti]>0.15){c.health-=6+G.fire[ti]*16;c.warm=max(0,c.warm-8);}
    if(c.pi>=c.path.length){c.moving=false;return true;}
    return false;
  }
  c.x+=dx/d*sp; c.y+=dy/d*sp;
  c.tx=floor(c.x); c.ty=floor(c.y);
  c.walk+=sp*3.6; c.moving=true;
  return false;
}

/* ── needs ────────────────────────────────────────────────────────────── */
function isNight(){const h=(G.t.min/60)%24;return h<6||h>=20;}
function dayLight(){
  const h=(G.t.min/60)%24;
  // 0 = pitch black, 1 = full day
  const rise=smooth(sat((h-5.2)/1.4));
  const set=1-smooth(sat((h-18.4)/1.7));
  let l=min(rise,set);
  l*= (G.wx.type==="clear"?1:WEATHER[G.wx.type].light*0.55+0.45);
  return clamp(l,0.055,1);
}
function tempNow(){
  const S=SEASONS[G.season];
  const h=(G.t.min/60)%24;
  const diurnal=Math.sin((h-9)/24*TAU)*0.5+0.5;
  let t=lerp(S.temp[0],S.temp[1],diurnal);
  if(G.wx.type==="rain")t-=2; if(G.wx.type==="snow")t-=3; if(G.wx.type==="storm")t-=4;
  if(G.wx.type==="clear"&&isNight())t-=2.5;
  const harsh=MD().harsh||0;
  if(harsh)t-=harsh*(G.season===3?3.4:1.4);
  return t;
}

function needsTick(c,dt){
  const eatRate=c.traits.includes("comi")?1.5:1.0;
  c.hunger-=dt*0.28*eatRate*(c.moving?1.12:0.92);
  const load=c.state==="working"?1.5:(c.moving?1.05:0.5);
  c.energy-=dt*0.44*load*(isNight()&&c.traits.includes("notu")?0.75:1);
  if(G.temp<2&&!c.clothes&&c.home)c.warm-=dt*0.9;
  else if(G.temp<2&&!c.clothes)c.warm-=dt*2.1;
  else c.warm=min(100,c.warm+dt*7);

  c.hunger=clamp(c.hunger,0,100);c.energy=clamp(c.energy,0,100);c.warm=clamp(c.warm,0,100);

  if(c.hunger<=0)c.health-=dt*1.5;
  if(c.warm<=6&&G.temp<3)c.health-=dt*1.1;
  if(c.hunger>62&&c.energy>42&&c.warm>30)c.health=min(100,c.health+dt*(c.inInf?1.5:0.32));
  c.health=clamp(c.health,0,100);

  // mood target
  let m=c.traits.includes("aleg")?72:(c.traits.includes("tris")?44:58);
  if(c.hunger<45)m-=(45-c.hunger)*0.62;
  if(c.hunger<15)m-=16;
  if(c.energy<32)m-=(32-c.energy)*0.5;
  if(c.warm<35)m-=(35-c.warm)*0.4;
  m-=(100-c.health)*0.42;
  if(c.home&&c.bed!=null)m+=(c.home.def==="camp"?2:9+c.home.quality*5); else m-=13;
  if(c.clothes&&G.temp<6)m+=6;
  const daysFood=G.stock.food/max(1,aliveCols().length);
  if(daysFood<3)m-=14; else if(daysFood>8)m+=5;
  if(G.buff.festival>0)m+=18;
  if(G.moodShock>0)m-=G.moodShock*0.9;
  if(c.idleT>26)m-=7;
  // ambience from pretty buildings
  m+=c.moodBonus||0;
  c.moodTarget=clamp(m,2,100);
  c.mood+=(c.moodTarget-c.mood)*min(1,dt*0.055);
  c.mood=clamp(c.mood,0,100);

  if(c.thoughtT>0)c.thoughtT-=dt; else c.thought="";
  if(c.health<=0){
    const cause=c.hunger<=0?"fome":(c.warm<=6?"hipotermia":(c.wound||"ferimentos"));
    killColonist(c,cause);
  }
  // mental break
  if(c.mood<14&&c.breakT<=0&&chance(dt*0.02)){c.breakT=14;c.job&&(c.job.by=0);c.job=null;
    notify("Crise nervosa",c.first+" entrou em colapso e abandonou o trabalho.","bad");}
  if(c.breakT>0)c.breakT-=dt;
  // tools & clothes provisioning
  if(!c.tool&&G.stock.tools>0){G.stock.tools--;c.tool=true;c.thought="Ferramenta nova!";c.thoughtT=5;}
  if(G.season===3&&!c.clothes&&G.stock.cloth>=2){G.stock.cloth-=2;c.clothes=true;}
  if(G.season===0)c.clothes=false;
}

/* ── job execution ────────────────────────────────────────────────────── */
function acquireJob(c){
  const j=bestJob(c);
  if(!j){c.state="idle";c.stateTxt="Ocioso";return false;}
  j.by=c.id; c.job=j; c.phase="to"; c.workT=0;
  const ok=routeToJob(c,j);
  if(!ok){releaseJob(c);return false;}
  return true;
}
function releaseJob(c){
  if(c.job){
    const j=c.job;
    j.by=0;j.prog=0;
    if(j.type==="haul"&&j.item){
      const it=G.items.find(i=>i&&i.id===j.item);
      if(!it||it.dead)j.dead=true;
      else if(it.taken===c.id)it.taken=0;
    }
  }
  c.job=null;c.phase="";c.state="idle";c.stateTxt="Ocioso";c.path=null;c.moving=false;
  // never let a colonist end up permanently holding goods they have nowhere to take
  if(c.carry&&c.carry.amount>0){dropItem(c.carry.kind,c.carry.amount,c.tx,c.ty,true);c.carry=null;}
}
function routeToJob(c,j){
  if(j.type==="haul"){
    const it=G.items.find(i=>i&&i.id===j.item);
    if(!it||it.dead){j.dead=true;return false;}
    if(it.taken&&it.taken!==c.id)return false;
    it.taken=c.id; j.x=it.x;j.y=it.y;
    const ok=moveTo(c,it.x,it.y);
    if(!ok){j.coolU=G.t.min+40;it.taken=0;}
    return ok;
  }
  if(j.type==="defend"){
    const e=jobTarget(j);
    if(!e){j.dead=true;return false;}
    j.x=floor(e.x);j.y=floor(e.y);
    return moveTo(c,clamp(j.x,0,MAP_W-1),clamp(j.y,0,MAP_H-1));
  }
  if(j.type==="heal"){
    const p=G.cols[j.patient];
    if(!p||!p.alive){j.dead=true;return false;}
    j.x=floor(p.x);j.y=floor(p.y);
    return moveTo(c,j.x,j.y);
  }
  if(j.bx){
    const b=G.buildings[j.bx];
    if(!b||b.dead){j.dead=true;return false;}
    if(b.w===1&&b.h===1&&G.cost[idx(b.x,b.y)]<90)return moveTo(c,b.x,b.y);
    const p=pathToArea(c.tx,c.ty,b.x,b.y,b.w,b.h);
    if(p){setPath(c,p);return true;}
    j.coolU=G.t.min+40;return false;
  }
  if(j.node){
    const n=G.nodes[j.node];
    if(!n||n.dead){j.dead=true;return false;}
    j.x=n.x;j.y=n.y;
    const p=pathToArea(c.tx,c.ty,n.x,n.y,1,1);
    if(p){setPath(c,p);return true;}
    j.coolU=G.t.min+40;return false;
  }
  return moveTo(c,j.x,j.y);
}

function completeJob(c,j){
  const sk=SKILL_OF[j.type];
  switch(j.type){
    case "chop": case "mine": case "gather": {
      const n=G.nodes[j.node];
      if(!n||n.dead)break;
      const d=NODEDEF[n.kind];
      const mul=c.traits.includes("verd")&&j.type==="gather"?1.5:1;
      giveYield(d.yield,n.x,n.y,(0.85+c.skill[sk]*0.03)*mul);
      for(let i=0;i<10;i++)spawnParticle(n.x+.5,n.y+.5,n.kind<=3||n.kind===7?"leaf":"dust");
      if(n.kind===N.OAK||n.kind===N.PINE||n.kind===N.BIRCH){Audio_.chop();G.stats.chopped++;
        spawnFloat(n.x+.5,n.y,"+"+d.yield.wood+" madeira","#c98f4e");}
      else if(n.kind===N.BOULDER||n.kind===N.ORE){Audio_.mine();spawnFloat(n.x+.5,n.y,"+"+d.yield.stone+" pedra","#c3ccd8");}
      else {Audio_.harvest();G.stats.harvested++;}
      if(d.regrow){n.amount=0;n.marked=false;n.regrowT=d.regrow;n.hidden=true;
        recomputeCostLocal(n.x,n.y);}
      else delNode(n);
      gainXP(c,sk,j.work*2.4);
      break;
    }
    case "build": {
      const b=G.buildings[j.bx];
      if(b&&!b.dead&&b.built>=1){
        G.stats.built++;
        notify("Construção concluída",BDEF[b.def].name+" está pronta.","good");
        spawnFloat(b.x+b.w/2,b.y,"✓ "+BDEF[b.def].name,"#5fd69b");
        for(let i=0;i<16;i++)spawnParticle(b.x+rand(0,b.w),b.y+rand(0,b.h),"spark");
        Audio_.bell();
        if(b.def==="house"){b.beds=BDEF.house.beds;assignHomes();}
        if(BDEF[b.def].prestige)addPrestige(BDEF[b.def].prestige,BDEF[b.def].name+" erguido");
        invalidateDrop();
      }
      gainXP(c,"construction",j.work*2.6); c.built++;
      break;
    }
    case "till": {
      const b=G.buildings[j.bx]; if(b){b.tilled=true;b.stage=0;b.growth=0;
        for(let i=0;i<8;i++)spawnParticle(b.x+rand(0,b.w),b.y+rand(0,b.h),"dust");}
      gainXP(c,"farming",4); break;
    }
    case "sow": {
      const b=G.buildings[j.bx]; if(b){b.stage=1;b.growth=0;}
      gainXP(c,"farming",3); break;
    }
    case "harvest": {
      const b=G.buildings[j.bx];
      if(b){
        const cd=CROPS[b.crop];
        let mul=(0.8+c.skill.farming*0.045)*(0.6+G.fer[idx(b.x+1,b.y+1)]/100*0.7);
        if(c.traits.includes("verd"))mul*=1.5;
        for(const k in cd.yield){
          const amt=max(1,round(cd.yield[k]*mul));
          dropItem(k,amt,b.x+1,b.y+1);
          spawnFloat(b.x+1.5,b.y+1,"+"+amt+" "+(k==="food"?"comida":"tecido"),k==="food"?"#e8c25a":"#c9a3d6");
        }
        b.stage=0;b.growth=0;b.tilled=chance(.75);
        G.stats.harvested++; Audio_.harvest();
        for(let i=0;i<10;i++)spawnParticle(b.x+rand(0,b.w),b.y+rand(0,b.h),"leaf");
      }
      gainXP(c,"farming",6); c.harvested++;
      break;
    }
    case "mine2": {
      const b=G.buildings[j.bx];
      if(b){const amt=3+round(c.skill.mining*0.4);
        dropItem("stone",amt,b.x,b.y);
        if(chance(.14)){G.stock.coin+=2+randInt(0,4);spawnFloat(b.x+.5,b.y,"veio rico!","#e0a145");}
        spawnFloat(b.x+.5,b.y,"+"+amt+" pedra","#c3ccd8");Audio_.mine();}
      gainXP(c,"mining",7); break;
    }
    case "craft": {
      const b=G.buildings[j.bx]; const r=RECIPES[j.recipe];
      if(b&&r&&canAfford(r.in)){
        pay(r.in);
        for(const k in r.out)addStock(k,r.out[k]);
        if(r.buff){G.buff[r.buff]=3*24*60;notify("Festival!",b? "A cerveja foi servida. A colônia celebra por 3 dias.":"",  "epic");Audio_.bell();}
        if(r.furnish){
          let best=null;
          for(const h of G.buildings)if(h&&!h.dead&&h.def==="house"&&h.built>=1&&h.quality<3)if(!best||h.quality<best.quality)best=h;
          if(best){best.quality++;spawnFloat(best.x+1,best.y,"casa melhorada","#f2b45c");assignHomes();}
          else {addStock("wood",2);}
        }
        if(r.out.tools)spawnFloat(b.x+.5,b.y,"+1 ferramenta","#b9c4d2");
        for(let i=0;i<8;i++)spawnParticle(b.x+rand(0,b.w),b.y+rand(0,b.h),"spark");
        Audio_.build();
        if(b.queue.length)b.queue.shift();
      }
      gainXP(c,"crafting",6); break;
    }
    case "water": {
      const i=idx(j.x,j.y);
      if(G.fire[i]>0){
        G.fire[i]=max(0,G.fire[i]-0.85);
        for(let k=0;k<12;k++)spawnParticle(j.x+.5+rand(-.3,.3),j.y+.5,"steam");
        if(G.fire[i]<=0){killJobsFor(x=>x.type==="water"&&x.x===j.x&&x.y===j.y);
          notify("Fogo contido","Um foco de incêndio foi apagado.","good");}
      }
      break;
    }
    case "heal": {
      const p=G.cols[j.patient];
      if(p&&p.alive){p.health=min(100,p.health+34);p.wound=null;
        spawnFloat(p.x,p.y,"+"+34+" saúde","#5fd69b");}
      gainXP(c,"medicine",8); break;
    }
    case "clear": {
      if(j.bx){const b=G.buildings[j.bx];if(b)demolish(b,false);}
      if(j.node){const n=G.nodes[j.node];if(n){
        if(n.kind<=3||n.kind===8)dropItem("wood",1,n.x,n.y);
        delNode(n);}}
      for(let i=0;i<8;i++)spawnParticle(j.x+.5,j.y+.5,"dust");
      break;
    }
  }
  j.dead=true;
}

function jobTick(c,dt){
  const j=c.job;
  if(!j||j.dead){releaseJob(c);return;}
  if(j.type==="defend"){
    const e=jobTarget(j);
    if(!e){j.dead=true;releaseJob(c);return;}
    const d=dist(c.x,c.y,e.x,e.y);
    if(d>1.35){
      if(!c.moving||c.repathT<=0){
        const p=findPath(c.tx,c.ty,clamp(floor(e.x),0,MAP_W-1),clamp(floor(e.y),0,MAP_H-1));
        if(p)setPath(c,p);
        c.repathT=0.5;
      }
      moveAlong(c,dt);
      c.state="moving";c.stateTxt="Em marcha";
      return;
    }
    c.state="fighting";c.stateTxt=j.hunt?"Caçando":"Combatendo";
    c.attackT-=dt;
    if(c.attackT<=0){
      c.attackT=1.05;
      const dmg=(4+c.skill.fighting*1.1+(c.tool?2.5:0))*(c.traits.includes("fort")?1.4:1)*(c.traits.includes("brav")?1.3:1)*(garrisonOn()?1.25:1);
      hurtEnemy(e,dmg,c);
      gainXP(c,"fighting",2.2);
      Audio_.noise(.07,.1,1600,1.4,"highpass");
    }
    return;
  }
  if(j.type==="haul"){
    if(c.phase==="to"){
      const it=G.items.find(i=>i&&i.id===j.item);
      if(!it||it.dead){j.dead=true;releaseJob(c);return;}
      if(dist(c.x,c.y,it.x+.5,it.y+.5)<1.62){
        const take=min(it.amount,carryCap(c)-(c.carry&&c.carry.kind===it.kind?c.carry.amount:0));
        if(take<=0){j.coolU=G.t.min+40;releaseJob(c);return;}
        it.amount-=take;
        if(it.amount<=0){it.dead=true;}
        else it.taken=0;
        if(c.carry&&c.carry.kind===it.kind)c.carry.amount+=take; else c.carry={kind:it.kind,amount:take};
        c.phase="drop";
        // pick nearest drop point
        const dps=dropPoints();
        if(!dps||!dps.length){j.dead=true;releaseJob(c);return;}
        let bd=null,bv=1e9;
        for(const d of dps){const v=dist2(c.tx,c.ty,d.x,d.y);if(v<bv){bv=v;bd=d;}}
        c.dropPt=bd;
        const p=findPath(c.tx,c.ty,bd.x,bd.y);
        if(!p){dropItem(c.carry.kind,c.carry.amount,c.tx,c.ty,true);c.carry=null;
          j.coolU=G.t.min+60;releaseJob(c);return;}
        setPath(c,p);
        Audio_.noise(.06,.07,800,1);
      } else {
        if(moveAlong(c,dt)&&dist(c.x,c.y,it.x+.5,it.y+.5)>=1.62){
          j.coolU=G.t.min+40; releaseJob(c);return;
        }
        c.state="moving";c.stateTxt="Buscar "+RESDEF[RESIX[it.kind]].name.toLowerCase();
      }
      return;
    }
    if(c.phase==="drop"){
      if(moveAlong(c,dt)){
        const got=addStock(c.carry.kind,c.carry.amount);
        if(got<c.carry.amount){
          dropItem(c.carry.kind,c.carry.amount-got,c.tx,c.ty,true);
          if(G._fullDay!==G.t.day){G._fullDay=G.t.day;
            notify("Armazéns cheios","Sem espaço para o excedente. Construa um Depósito.","bad");}
        }
        if(got>0){
          spawnFloat(c.x,c.y,"+"+got+" "+RESDEF[RESIX[c.carry.kind]].name.toLowerCase(),RESDEF[RESIX[c.carry.kind]].col);
          G.flow[c.carry.kind]+=got;
          Audio_.noise(.08,.09,520,.9);
        }
        c.carry=null; j.dead=true; releaseJob(c);
      }
      c.state="hauling";c.stateTxt="Carregando";
      return;
    }
  }
  // generic: move then work
  if(c.phase==="to"){
    if(j.bx){
      const b=G.buildings[j.bx];
      if(!b||b.dead){j.dead=true;releaseJob(c);return;}
      if(b.w>1||b.h>1||G.cost[idx(b.x,b.y)]>=90){
        // need adjacency
        if(!c.path){
          const p=pathToArea(c.tx,c.ty,b.x,b.y,b.w,b.h);
          if(!p){j.coolU=G.t.min+40;releaseJob(c);return;}
          setPath(c,p);
        }
      }
    }
    const done=moveAlong(c,dt);
    c.state="moving";
    c.stateTxt=({build:"Indo construir",till:"Indo arar",sow:"Indo semear",harvest:"Indo colher",
      craft:"Indo à oficina",water:"Indo buscar água",heal:"Indo tratar",clear:"Indo demolir",
      chop:"Indo cortar",mine:"Indo minerar",gather:"Indo coletar",mine2:"Indo à mina"})[j.type]||"Em marcha";
    if(done){
      // verify still in range for multi-tile
      if(j.bx){
        const b=G.buildings[j.bx];
        if(b&&(b.w>1||b.h>1)&&!(c.tx>=b.x-1&&c.tx<=b.x+b.w&&c.ty>=b.y-1&&c.ty<=b.y+b.h)){
          releaseJob(c);return;
        }
      }
      c.phase="work";c.workT=0;
    }
    return;
  }
  if(c.phase==="work"){
    c.state="working";
    const nm=({build:"Construindo",till:"Arando",sow:"Semeando",harvest:"Colhendo",craft:"Fabricando",
      water:"Apagando fogo",heal:"Tratando ferido",clear:"Demolindo",chop:"Cortando lenha",
      mine:"Minerando",mine2:"Extraindo",gather:"Coletando"})[j.type]||"Trabalhando";
    c.stateTxt=nm;
    c.workT+=dt*workSpeed(c);
    if(chance(dt*2.2)){
      const pt=j.node?G.nodes[j.node]:null;
      const px=pt?pt.x+.5:(j.bx?G.buildings[j.bx].x+G.buildings[j.bx].w/2:j.x+.5);
      const py=pt?pt.y+.5:(j.bx?G.buildings[j.bx].y+G.buildings[j.bx].h/2:j.y+.5);
      spawnParticle(px+rand(-.3,.3),py+rand(-.2,.2),
        j.type==="build"?"dust":(j.type==="chop"?"chip":(j.type==="mine"||j.type==="mine2"?"spark":(j.type==="harvest"||j.type==="gather"?"leaf":"dust"))));
    }
    if(j.type==="build"){
      const b=G.buildings[j.bx];
      if(b){b.work+=dt*workSpeed(c);b.built=clamp(b.work/b.workNeed,0,1);
        if(b.built>=1){completeJob(c,j);return;}
        if(chance(dt*1.6))Audio_.build();}
    } else if(j.type==="chop"||j.type==="mine"||j.type==="gather"){
      const n=G.nodes[j.node];
      if(!n||n.dead){j.dead=true;releaseJob(c);return;}
      n.chopT=(n.chopT||0)+dt*workSpeed(c);
      const need=NODEDEF[n.kind].work*(c.tool?0.8:1);
      if(chance(dt*2.0)){if(j.type==="chop")Audio_.chop();else if(j.type==="mine")Audio_.mine();else Audio_.harvest();}
      if(n.chopT>=need){completeJob(c,j);return;}
    } else if(j.type==="craft"){
      if(chance(dt*1.4))Audio_.build();
    }
    if(c.workT>=j.work){completeJob(c,j);}
    else j.prog=c.workT/j.work;
  }
}

/* ── colonist master update ───────────────────────────────────────────── */
function updateColonist(c,dt){
  if(!c.alive)return;
  c.repathT=(c.repathT||0)-dt;
  c.idleT=c.state==="idle"?c.idleT+dt:0;
  needsTick(c,dt);
  if(!c.alive)return;
  c.speedMul=1*(c.carry?0.86:1)*(G.wx.type==="snow"?0.86:1)*(c.energy<20?0.82:1)*(c.health<50?0.8:1)*(G.temp<0?0.9:1);

  // threat response
  const threat=nearestThreat(c);
  if(threat){
    const brave=c.traits.includes("brav");
    if(c.militia||brave){
      if(!c.job||c.job.type!=="defend"||c.job.enemy!==threat.id){
        if(c.job)releaseJob(c);
        const j=addJob({type:"defend",x:floor(threat.x),y:floor(threat.y),enemy:threat.id,prio:30,work:999,skill:"fighting"});
        c.job=j;j.by=c.id;c.phase="to";
      }
      jobTick(c,dt); return;
    } else if(!brave||c.traits.includes("medr")){
      if(c.job)releaseJob(c);
      c.state="fleeing";c.stateTxt="Fugindo!";
      if(!c.path||c.repathT<=0){
        const ax=clamp(c.tx*2-floor(threat.x),1,MAP_W-2), ay=clamp(c.ty*2-floor(threat.y),1,MAP_H-2);
        let bx=c.tx,by=c.ty,bd=-1;
        for(let a=0;a<10;a++){
          const ang=a/10*TAU, tx2=clamp(c.tx+Math.cos(ang)*9|0,1,MAP_W-2), ty2=clamp(c.ty+Math.sin(ang)*9|0,1,MAP_H-2);
          const d=dist2(tx2,ty2,threat.x,threat.y);
          if(d>bd&&G.cost[idx(tx2,ty2)]<90){bd=d;bx=tx2;by=ty2;}
        }
        const p=findPath(c.tx,c.ty,bx,by,2500); if(p)setPath(c,p);
        c.repathT=1.2;
      }
      moveAlong(c,dt);
      return;
    }
  }

  // eating — a loaf from the communal oven beats a handful of raw stores
  if(c.hunger<34&&edible()>=1&&c.phase!=="eat"){
    if(c.job&&c.job.prio<20)releaseJob(c);
    if(!c.job){
      const br=takeMeal(c);
      c.phase="eat";c.state="eating";c.stateTxt="Comendo";c.eatT=2.2;
      spawnFloat(c.x,c.y,br?"+pão":"+comida",br?"#d79a4e":"#e8c25a");
      c.thought=br?"Pão quente. Valeu.":"Que refeição.";c.thoughtT=6;
    }
    else if(c.hunger<12){takeMeal(c);c.phase="eat";c.state="eating";c.eatT=2.2;}
  }
  if(c.phase==="eat"){c.eatT-=dt;moveAlong(c,dt*0.2);if(c.eatT<=0){c.phase="";c.job=null;}return;}

  // sleeping
  const night=isNight();
  if((c.energy<22||(night&&c.energy<62))&&c.state!=="sleeping"){
    if(c.job&&c.job.prio<20)releaseJob(c);
    if(!c.job){
      c.state="sleeping";c.phase="sleep";
      if(c.home&&c.bed!=null){
        const b=c.home;
        const tx=clamp(b.x+ (c.bed%b.w), b.x, b.x+b.w-1), ty=clamp(b.y+((c.bed/b.w)|0),b.y,b.y+b.h-1);
        const p=pathToArea(c.tx,c.ty,b.x,b.y,b.w,b.h);
        c.sleepHome=!!p;
        if(p)setPath(c,p);
      } else {c.sleepHome=false;c.lastHomeless=G.t.day;}
      c.stateTxt=c.sleepHome?"Dormindo em casa":"Dormindo ao relento";
    }
  }
  if(c.state==="sleeping"){
    moveAlong(c,dt);
    const rate=c.sleepHome?7.2:3.1;
    c.energy=min(100,c.energy+dt*rate);
    if(c.sleepHome&&c.home)c.mood=min(100,c.mood+dt*0.5*(1+c.home.quality*0.4));
    else c.mood=max(0,c.mood-dt*0.35);
    if(c.inInf)c.health=min(100,c.health+dt*1.2);
    if(c.energy>96||(!night&&c.energy>60)){c.state="idle";c.phase="";c.stateTxt="Acordando";}
    return;
  }

  // healing at infirmary
  if(c.health<55){
    const inf=G.buildings.find(b=>b&&!b.dead&&b.def==="infirm"&&b.built>=1);
    if(inf&&c.state!=="healing"&&c.energy>40){
      c.state="healing";c.stateTxt="Recuperando";
      const p=pathToArea(c.tx,c.ty,inf.x,inf.y,inf.w,inf.h); if(p)setPath(c,p);
      c.inInf=true;
    }
    if(c.state==="healing"){
      moveAlong(c,dt);
      c.health=min(100,c.health+dt*2.2);
      c.energy=min(100,c.energy+dt*2);
      if(c.health>=92){c.state="idle";c.inInf=false;}
      return;
    }
  }
  // medic tending to the wounded
  if(c.skill.medicine>=2&&c.state==="idle"){
    const hurt=aliveCols().find(p=>p.alive&&p.health<50&&!p.beingTended);
    if(hurt&&G.buildings.some(b=>b&&!b.dead&&b.def==="infirm"&&b.built>=1)){
      hurt.beingTended=true;
      const j=addJob({type:"heal",x:floor(hurt.x),y:floor(hurt.y),patient:hurt.id,prio:16,work:3,skill:"medicine"});
      c.job=j;j.by=c.id;c.phase="to";
    }
  }

  // mental break → wander
  if(c.breakT>0){
    c.state="tantrum";c.stateTxt="Em crise";
    if(!c.moving&&chance(dt*1.2)){
      const tx=clamp(c.tx+randInt(-6,6),1,MAP_W-2), ty=clamp(c.ty+randInt(-6,6),1,MAP_H-2);
      const p=findPath(c.tx,c.ty,tx,ty,1800); if(p)setPath(c,p);
    }
    moveAlong(c,dt);
    if(chance(dt*.6))spawnParticle(c.x,c.y,"angry");
    return;
  }

  // working / seeking
  if(c.job){
    jobTick(c,dt);
    return;
  }
  c.seekT-=dt;
  if(c.seekT<=0){
    c.seekT=0.45+Math.random()*0.4;
    if(!acquireJob(c)){
      // nothing to do → socialise near a bonfire, else wander
      c.state="idle";
      c.socT=(c.socT||0)-dt;
      if(!c.moving&&c.socT<=0){
        c.socT=4+Math.random()*4;
        const bon=G.buildings.filter(b=>b&&!b.dead&&b.built>=1&&(BDEF[b.def].mood||b.def==="bonfire"));
        if(bon.length&&chance(.55)){
          const t=pick(bon);
          const p=pathToArea(c.tx,c.ty,t.x,t.y,t.w,t.h); if(p)setPath(c,p);
          c.stateTxt="Socializando";c.mood=min(100,c.mood+dt*1.2);
        } else {
          const tx=clamp(c.tx+randInt(-8,8),1,MAP_W-2), ty=clamp(c.ty+randInt(-8,8),1,MAP_H-2);
          const p=findPath(c.tx,c.ty,tx,ty,1500); if(p)setPath(c,p);
          c.stateTxt=c.mood>65?"Passeando":"Esperando ordens";
        }
      }
      moveAlong(c,dt);
    }
  } else {
    c.state="idle";
    moveAlong(c,dt);
  }
}

/* ── home assignment ──────────────────────────────────────────────────── */
const CAMP_BEDS=4;
function makeCampBld(){
  if(!G.camp){G.campBld=null;return null;}
  G.campBld={id:-1,def:"camp",x:G.camp.x,y:G.camp.y,w:2,h:2,quality:0,built:1,dead:false};
  return G.campBld;
}
function assignHomes(){
  const beds=[];
  for(const b of G.buildings){
    if(!b||b.dead||b.built<1)continue;
    const d=BDEF[b.def]; if(!d.beds)continue;
    const n=d.beds+b.quality;
    for(let i=0;i<n;i++)beds.push({b,slot:i});
  }
  if(G.campBld)for(let i=0;i<CAMP_BEDS;i++)beds.push({b:G.campBld,slot:i});
  const cols=aliveCols().slice().sort((a,b)=>b.mood-a.mood);
  for(const c of G.cols){if(c&&!c.alive){c.home=null;c.bed=null;}}
  for(let i=0;i<cols.length&&i<beds.length;i++){
    cols[i].home=beds[i].b; cols[i].bed=beds[i].slot;
  }
  G.housingCap=beds.length;
}

/* ── enemies & fauna ──────────────────────────────────────────────────── */
function spawnEnemy(kind,x,y){
  const D={wolf:{hp:34,dmg:6,speed:2.5,name:"Lobo",col:"#9aa4b2"},
           bandit:{hp:62,dmg:9,speed:1.9,name:"Salteador",col:"#c46a4e"},
           raider:{hp:96,dmg:13,speed:1.75,name:"Chefe invasor",col:"#a2453c"}}[kind];
  const e={id:G.eid++,kind,x:x+.5,y:y+.5,tx:x,ty:y,hp:D.hp,maxhp:D.hp,dmg:D.dmg,speed:D.speed,
    name:D.name,col:D.col,dead:false,path:null,pi:0,target:null,attackT:0,walk:0,dir:0,
    state:"hunt",repathT:0,flee:0,anim:Math.random()*TAU};
  G.enemies.push(e);
  return e;
}
function jobTarget(j){
  if(!j||!j.enemy)return null;
  const list=j.hunt?G.animals:G.enemies;
  for(let i=0;i<list.length;i++){const e=list[i];if(e&&e.id===j.enemy&&!e.dead)return e;}
  return null;
}
function hurtEnemy(e,dmg,by){
  e.hp-=dmg;
  spawnFloat(e.x,e.y-0.3,round(dmg),"#ff9c8a");
  for(let i=0;i<5;i++)spawnParticle(e.x,e.y,"blood");
  if(e.hp<=0){
    e.dead=true; G.stats.killed++;
    if(by){by.kills=(by.kills||0)+1;gainXP(by,"fighting",e.animal?5:10);}
    if(e.animal){
      const meat=e.kind==="deer"?randInt(7,13):randInt(1,3);
      dropItem("food",meat,floor(e.x),floor(e.y));
      if(e.kind==="deer")dropItem("cloth",randInt(1,3),floor(e.x),floor(e.y));
      spawnFloat(e.x,e.y,"+"+meat+" comida","#e8c25a");
      notify("Caçada bem-sucedida",by?by.first:"Um colono"+" abateu um "+e.name.toLowerCase()+".","good");
      for(let i=0;i<12;i++)spawnParticle(e.x,e.y,"blood");
      return;
    }
    notify(e.kind==="wolf"?"Lobo abatido":"Invasor abatido", e.name+" foi morto por "+(by?by.first:"a colônia")+".","good");
    for(let i=0;i<16;i++)spawnParticle(e.x,e.y,"blood");
    if(e.kind!=="wolf")dropItem("food",randInt(2,6),floor(e.x),floor(e.y));
    if(e.kind==="bandit"||e.kind==="raider"){G.stock.coin+=randInt(6,22);}
  } else if(e.kind==="wolf"&&e.hp<e.maxhp*0.3){e.flee=8;}
    else if(e.animal){e.flee=6;}
}
function nearestThreat(c){
  let best=null,bd=1e9;
  for(const e of G.enemies){
    if(!e||e.dead||e.flee>0)continue;
    const d=dist2(c.x,c.y,e.x,e.y);
    if(d<bd&&d<(e.kind==="wolf"?130:190)){bd=d;best=e;}
  }
  return best;
}
function updateEnemy(e,dt){
  if(e.dead)return;
  e.anim+=dt*6;
  if(e.flee>0){
    e.flee-=dt;
    if(!e.path||e.repathT<=0){
      const ang=Math.random()*TAU;
      const tx=clamp(floor(e.x+Math.cos(ang)*18),1,MAP_W-2), ty=clamp(floor(e.y+Math.sin(ang)*18),1,MAP_H-2);
      const p=findPath(e.tx,e.ty,tx,ty,1600); if(p)setPathE(e,p); e.repathT=1.4;
    }
    moveE(e,dt);
    if(e.flee<=0)e.dead=true;
    return;
  }
  // choose target: nearest colonist, else nearest building
  e.repathT-=dt;
  let tgt=null,td=1e9;
  for(const c of G.cols){
    if(!c||!c.alive)continue;
    const d=dist2(e.x,e.y,c.x,c.y);
    if(d<td){td=d;tgt={type:"col",o:c,x:c.x,y:c.y};}
  }
  if(e.kind!=="wolf"){
    for(const b of G.buildings){
      if(!b||b.dead||b.built<1)continue;
      const d=dist2(e.x,e.y,b.x+b.w/2,b.y+b.h/2);
      if(d<td*0.55){td=d;tgt={type:"bld",o:b,x:b.x+b.w/2,y:b.y+b.h/2};}
    }
  }
  if(!tgt){e.dead=true;return;}
  e.target=tgt;
  const d=dist(e.x,e.y,tgt.x,tgt.y);
  if(d>1.25){
    if(!e.path||e.repathT<=0){
      let p=null;
      if(tgt.type==="bld")p=pathToArea(e.tx,e.ty,tgt.o.x,tgt.o.y,tgt.o.w,tgt.o.h);
      else p=findPath(e.tx,e.ty,clamp(floor(tgt.x),0,MAP_W-1),clamp(floor(tgt.y),0,MAP_H-1),2600);
      if(p)setPathE(e,p);
      e.repathT=0.85;
    }
    moveE(e,dt);
  } else {
    e.attackT-=dt;
    if(e.attackT<=0){
      e.attackT=1.15;
      if(tgt.type==="col"){
        const c=tgt.o;
        if(c.alive){
          const block=c.tool?0.75:1;
          c.health-=e.dmg*block;c.wound="ferimento de "+e.name.toLowerCase();
          spawnFloat(c.x,c.y-0.3,round(e.dmg*block),"#f0685a");
          for(let i=0;i<6;i++)spawnParticle(c.x,c.y,"blood");
          if(c.health<=0)killColonist(c,"ataque de "+e.name.toLowerCase());
        }
      } else {
        const b=tgt.o;
        if(b&&!b.dead){
          b.hp-=e.dmg*1.6;
          for(let i=0;i<4;i++)spawnParticle(b.x+rand(0,b.w),b.y+rand(0,b.h),"dust");
          if(b.hp<=0){
            if(chance(.4)&&BDEF[b.def].cost.wood)ignite(b.x,b.y,0.9);
            destroyBuilding(b,"invasores");
          } else if(e.kind!=="wolf"&&b.def==="stock"&&chance(.5)){
            const k=pick(["wood","stone","food","cloth"]);
            const amt=min(G.stock[k],randInt(4,14));
            if(amt>0){G.stock[k]-=amt;spawnFloat(b.x+b.w/2,b.y,"-"+amt+" "+k,"#f0685a");}
          }
        }
      }
    }
  }
}
function setPathE(e,p){e.path=p;e.pi=p?1:0;if(p&&p.length>1){const t=p[0];e.x=t%MAP_W+.5;e.y=((t/MAP_W)|0)+.5;}}
function moveE(e,dt){
  if(!e.path||e.pi>=e.path.length)return;
  const ti=e.path[e.pi],tx=ti%MAP_W,ty=(ti/MAP_W)|0;
  const cx=tx+.5,cy=ty+.5,dx=cx-e.x,dy=cy-e.y,d=Math.hypot(dx,dy)||1e-6;
  let cost=G.cost[ti]; if(cost>=90)cost=2.2;
  const sp=e.speed*(1/cost)*dt*(G.wx.type==="snow"?0.85:1);
  e.dir=Math.atan2(dy,dx);
  if(d<=sp){e.x=cx;e.y=cy;e.pi++;e.tx=tx;e.ty=ty;}
  else {e.x+=dx/d*sp;e.y+=dy/d*sp;e.tx=floor(e.x);e.ty=floor(e.y);}
  e.walk+=sp*4;
}
function spawnAnimal(kind,x,y){
  const e={id:G.aid++,kind,x:x+.5,y:y+.5,tx:x,ty:y,animal:true,dead:false,hp:kind==="deer"?22:8,
    maxhp:kind==="deer"?22:8,dmg:0,speed:kind==="deer"?2.6:1.4,name:kind==="deer"?"Cervo":"Coelho",
    path:null,pi:0,walk:0,dir:0,repathT:0,anim:Math.random()*TAU,wander:0,state:"graze",flee:0,
    col:kind==="deer"?"#a8764a":"#c9bfae"};
  G.animals.push(e);
  return e;
}
function updateAnimal(a,dt){
  if(a.dead)return;
  a.anim+=dt*5;
  // flee from colonists / predators
  let scare=0,sx=0,sy=0;
  for(const c of G.cols){if(!c||!c.alive)continue;const d=dist2(a.x,a.y,c.x,c.y);if(d<42){scare=1;sx=c.x;sy=c.y;}}
  for(const e of G.enemies){if(e.dead)continue;const d=dist2(a.x,a.y,e.x,e.y);if(d<60){scare=1;sx=e.x;sy=e.y;}}
  a.flee=max(0,(a.flee||0)-dt);
  if(scare)a.flee=3.2;
  a.repathT-=dt;
  if(a.flee>0){
    if(!a.path||a.repathT<=0){
      const ang=Math.atan2(a.y-sy,a.x-sx)+rand(-.5,.5);
      const tx=clamp(floor(a.x+Math.cos(ang)*10),1,MAP_W-2),ty=clamp(floor(a.y+Math.sin(ang)*10),1,MAP_H-2);
      const p=findPath(a.tx,a.ty,tx,ty,1400);if(p)setPathE(a,p);a.repathT=1.1;
    }
    moveE(a,dt*1.25);
  } else {
    a.wander-=dt;
    if(a.wander<=0){
      a.wander=rand(2.5,7);
      if(chance(.72)){
        const tx=clamp(a.tx+randInt(-5,5),1,MAP_W-2),ty=clamp(a.ty+randInt(-5,5),1,MAP_H-2);
        if(G.cost[idx(tx,ty)]<90){const p=findPath(a.tx,a.ty,tx,ty,900);if(p)setPathE(a,p);}
      } else a.path=null;
    }
    moveE(a,dt*0.55);
    a.state=a.path?"walk":"graze";
  }
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 7 · time, seasons, weather, particles, economy, events, main tick
═══════════════════════════════════════════════════════════════════════════════*/

// MIN_PER_SEC · SPEEDS · DAY_MIN · DT_DAY live with the map constants (Part 2)

/* ── particles ────────────────────────────────────────────────────────── */
const PART={
  dust:  {life:[.4,.8], col:[[150,132,104],[120,104,82]], size:[1.5,3.4], vy:[6,16],  g:-14, spread:16},
  leaf:  {life:[.9,1.7],col:[[126,164,72],[196,158,64],[168,110,52]], size:[2,3.6], vy:[4,12], g:6, spin:6, spread:22},
  spark: {life:[.3,.6], col:[[255,214,140],[255,168,80]], size:[1.2,2.4], vy:[10,34], g:52, spread:30},
  chip:  {life:[.5,.95],col:[[168,120,64],[122,86,46]], size:[1.6,3.2], vy:[8,26], g:60, spread:26},
  smoke: {life:[1.6,3.0],col:[[70,66,64],[110,104,100]],size:[3,8],   vy:[10,20], g:-6, spread:6, fade:.5},
  steam: {life:[.7,1.3],col:[[210,224,236],[240,248,255]],size:[3,7], vy:[14,26], g:-10,spread:14,fade:.6},
  blood: {life:[.5,.9], col:[[168,42,38],[122,26,26]], size:[1.6,3.4],vy:[8,26], g:70, spread:34},
  fire:  {life:[.4,.8], col:[[255,196,80],[255,110,40]],size:[2.5,5], vy:[22,42], g:-18,spread:10,add:true},
  angry: {life:[.9,1.3],col:[[240,104,90]], size:[4,5], vy:[14,20], g:0, spread:2},
  heart: {life:[1.1,1.6],col:[[240,120,140]],size:[3.5,5],vy:[12,18], g:-4, spread:6},
  petal: {life:[1.6,2.8],col:[[246,206,222],[255,232,240]],size:[1.8,3],vy:[6,14],g:2,spin:4,spread:20},
  snowp: {life:[2.4,4.0],col:[[238,246,255]],size:[1.4,2.8],vy:[10,18],g:0,spin:2,spread:14},
  drop:  {life:[.5,.9], col:[[120,178,226]], size:[1.2,2.2],vy:[26,40], g:80, spread:8},
};
function spawnParticle(x,y,type){
  if(G.particles.length>1400)return;
  const d=PART[type]||PART.dust;
  const a=Math.random()*TAU, r=Math.random()*d.spread;
  G.particles.push({
    x,y,type,life:d.life[0]+Math.random()*(d.life[1]-d.life[0]),max:0,
    vx:Math.cos(a)*r*0.35, vy:-(d.vy[0]+Math.random()*(d.vy[1]-d.vy[0])),
    size:d.size[0]+Math.random()*(d.size[1]-d.size[0]),
    col:pick(d.col), g:d.g||0, spin:d.spin?(Math.random()-.5)*d.spin:0, rot:Math.random()*TAU,
    add:!!d.add, fade:d.fade||1,
  });
  const p=G.particles[G.particles.length-1]; p.max=p.life;
}
function spawnFloat(x,y,txt,col){
  if(G.floats.length>60)G.floats.shift();
  G.floats.push({x,y,txt,col,life:1.5,max:1.5});
}
function updateParticles(dt){
  for(let i=G.particles.length-1;i>=0;i--){
    const p=G.particles[i];
    p.life-=dt;
    if(p.life<=0){G.particles.splice(i,1);continue;}
    p.vy+=p.g*dt;
    p.x+=p.vx*dt*0.045; p.y+=p.vy*dt*0.022;
    p.rot+=p.spin*dt;
    if(p.type==="smoke"||p.type==="steam"){p.vx+=Math.sin(p.life*3)*dt*4;p.size+=dt*3;}
  }
  for(let i=G.floats.length-1;i>=0;i--){
    const f=G.floats[i]; f.life-=dt; f.y-=dt*0.42;
    if(f.life<=0)G.floats.splice(i,1);
  }
}

/* ── weather ──────────────────────────────────────────────────────────── */
function weatherWeights(){
  const S=G.season;
  if(S===0)return{clear:34,clouds:26,rain:26,storm:7,fog:7,snow:0};
  if(S===1)return{clear:44,clouds:22,rain:18,storm:14,fog:2,snow:0};
  if(S===2)return{clear:28,clouds:28,rain:22,storm:6,fog:14,snow:2};
  return{clear:22,clouds:22,rain:4,storm:0,fog:12,snow:40};
}
function rollWeather(){
  const w=weatherWeights(); let tot=0; for(const k in w)tot+=w[k];
  let r=Math.random()*tot;
  for(const k in w){r-=w[k];if(r<=0)return k;}
  return "clear";
}
function setWeather(t){
  if(G.wx.type===t)return;
  G.wx.type=t;
  Audio_.setRain((t==="rain"||t==="storm")?1:(t==="snow"?0.55:(t==="fog"?0.22:0)));
}
function weatherTick(dt){
  G.wx.next-=dt*MIN_PER_SEC;
  if(G.wx.next<=0){
    const t=rollWeather();
    G.wx.next=rand(260,1500);
    setWeather(t);
    if(t==="storm")notify("Tempestade","Raios podem iniciar incêndios. Abriguem-se.","info");
    else if(t==="snow")notify("Nevasca","O frio castiga quem não tem abrigo e agasalho.","info");
    else if(t==="rain")notify("Chuva","As plantações agradecem; o trabalho desacelera.","info");
    else if(t==="fog")notify("Névoa","Visibilidade reduzida no vale.","info");
  }
  // lightning
  if(G.wx.type==="storm"){
    G.wx.lightning=max(0,G.wx.lightning-dt*3.4);
    if(chance(dt*0.055)){
      G.wx.lightning=1;
      Audio_.noise(.9,.22,180,.5,"lowpass");
      Audio_.tone(60,.8,"sawtooth",.09,.4);
      // maybe start a fire
      if(chance(.34)){
        for(let t=0;t<40;t++){
          const x=randInt(4,MAP_W-5),y=randInt(4,MAP_H-5),i=idx(x,y);
          if(fuelAt(i)>0.6){
            ignite(x,y,0.8);
            notify("Raio caiu!","Um incêndio começou no vale.","bad");
            banner("INCÊNDIO","um raio atingiu a floresta");
            Audio_.doom();
            break;
          }
        }
      }
    }
  } else G.wx.lightning=max(0,G.wx.lightning-dt*3.4);
}

/* ── prices & trade ───────────────────────────────────────────────────── */
function initPrices(){
  for(const r of RESDEF){
    if(r.k==="coin")continue;
    G.prices[r.k]={buy:r.base,sell:r.base*0.55,mom:0};
  }
}
function updatePrices(dt){
  const pop=max(1,aliveCols().length);
  const vol=MD().vol||1;
  for(const r of RESDEF){
    const k=r.k; if(k==="coin")continue;
    const p=G.prices[k]; if(!p)continue;
    // demand pressure: scarcity relative to need
    const need=({wood:pop*3+18,stone:pop*2+12,food:pop*6+14,cloth:pop*2+6,tools:pop*1.4+2,
      flour:pop*1.2+4,bread:pop*1.6+4})[k]||20;
    const supply=G.stock[k]+1;
    const ratio=need/supply;                       // >1 scarce → price up
    const target=clamp(r.base*Math.pow(ratio,0.42),r.base*0.42,r.base*2.9);
    p.mom=p.mom*0.985+(Math.random()-.5)*0.05*vol;
    p.buy+=(target-p.buy)*min(1,dt*0.06)+p.mom*dt;
    p.buy=clamp(p.buy,r.base*0.4,r.base*(vol>1.5?4.2:3.2));
    p.sell=p.buy*0.58;
  }
}
function priceMult(){return G.buildings.some(b=>b&&!b.dead&&b.def==="market"&&b.built>=1)?0.86:1;}
function makeCaravan(){
  const pool=["wood","stone","food","cloth","tools"];
  const goods=[];
  const n=randInt(3,5);
  const used=new Set();
  for(let i=0;i<n;i++){
    let k=pick(pool); let g=0;
    while(used.has(k)&&g++<12)k=pick(pool);
    used.add(k);
    goods.push({k,qty:randInt(12,44),sold:0,bought:0});
  }
  G.market.goods=goods;
  G.market.here=true;
  G.market.leave=3;  // days
  banner("CARAVANA","mercadores chegaram ao vale");
  notify("Caravana de mercadores","Eles ficarão por 3 dias. Abra o Comércio.","epic");
  Audio_.bell();
}

/* ── events ───────────────────────────────────────────────────────────── */
function wealth(){
  let w=stockTotal()*1.2+G.stock.coin*0.6;
  for(const b of G.buildings)if(b&&!b.dead&&b.built>=1)w+=Object.values(BDEF[b.def].cost).reduce((a,c)=>a+c,0)*1.4;
  return w;
}
function eventRoll(){
  const m=MD();
  const pop=aliveCols().length;
  const day=G.t.day;
  const rolls=[];
  // immigration
  const freeBeds=G.housingCap-pop;
  if(m.immigration){
    if(freeBeds>0&&avgMood()>52&&G.stock.food>pop*4)rolls.push({w:26+freeBeds*7,f:evImmigrants});
    if(freeBeds>2&&avgMood()>70)rolls.push({w:10,f:evImmigrants});
  }
  // traders
  if(!G.market.here&&(day>=G.market.next))rolls.push({w:200*m.caravan,f:()=>{makeCaravan();G.market.next=day+max(1,round(randInt(6,11)/m.caravan));}});
  // raids
  G.threat=clamp((wealth()/900+day*0.09+pop*0.22)*m.raid,0,100);
  if(m.raid>0&&day>5&&G.threat>7)rolls.push({w:(6+G.threat*1.5+(G.season===3?7:0))*m.raid,f:evRaid});
  // wolves in winter
  if((G.season===3||G.season===2)&&day>3)rolls.push({w:(9+(G.season===3?12:0))*(m.raid||0.5),f:evWolves});
  // disease
  if(pop>5)rolls.push({w:5+(m.harsh?5:0),f:evDisease});
  // birth
  if(pop>2&&freeBeds>0&&avgMood()>64)rolls.push({w:9,f:evBirth});
  // wandering traveller
  if(pop>1&&m.immigration)rolls.push({w:7,f:evWanderer});
  // bounty
  if(G.season===2)rolls.push({w:11,f:evBounty});
  // harsh modes get a frost warning
  if(m.harsh&&G.season===2&&G.seasonDay>=SEASON_DAYS-4)rolls.push({w:14,f:evFrost});
  // nothing
  rolls.push({w:52,f:null});
  let tot=0;for(const r of rolls)tot+=r.w;
  let x=Math.random()*tot;
  for(const r of rolls){x-=r.w;if(x<=0){if(r.f)r.f();return;}}
}
function evFrost(){
  for(const c of aliveCols()){c.warm=max(0,c.warm-26);if(!c.clothes)c.health-=6;}
  notify("Geada antecipada","O frio chegou antes do inverno. Sem agasalho ou lareira, a colônia adoece.","bad");
  Audio_.doom();
}
function edgeSpawnTile(pref){
  for(let t=0;t<260;t++){
    const side=randInt(0,3);
    let x,y;
    if(side===0){x=randInt(3,MAP_W-4);y=randInt(2,8);}
    else if(side===1){x=randInt(3,MAP_W-4);y=randInt(MAP_H-9,MAP_H-3);}
    else if(side===2){x=randInt(2,8);y=randInt(3,MAP_H-4);}
    else {x=randInt(MAP_W-9,MAP_W-3);y=randInt(3,MAP_H-4);}
    const b=G.bio[idx(x,y)];
    if(!BPASS[b])continue;
    if(G.res[idx(x,y)])continue;
    if(G.bld[idx(x,y)])continue;
    if(pref==="near"&&G.camp&&dist(x,y,G.camp.x,G.camp.y)>26)continue;
    if(pref==="far"&&G.camp&&dist(x,y,G.camp.x,G.camp.y)<20)continue;
    return {x,y};
  }
  return {x:randInt(6,MAP_W-7),y:randInt(6,MAP_H-7)};
}
function evImmigrants(){
  if(!MD().immigration)return;
  const free=G.housingCap-aliveCols().length;
  if(free<1)return;
  const n=min(randInt(1,3),free);
  const t=edgeSpawnTile("far");
  for(let i=0;i<n;i++){
    const c=makeColonist(clamp(t.x+i,1,MAP_W-2),t.y);
    spawnFloat(c.x,c.y,"novo colono","#5fd69b");
  }
  assignHomes();
  notify("Imigrantes chegaram",n+(n===1?" colono ouviu":" colonos ouviram")+" falar do vale e juntou-se a você.","good");
  banner("IMIGRANTES","+"+n+" colonos");
  Audio_.bell();
}
function evWanderer(){
  const t=edgeSpawnTile("far");
  const c=makeColonist(t.x,t.y,true);
  assignHomes();
  notify("Viajante solitário",c.name+", "+TRAIT.find(x=>x.id===c.traits[0]).name.toLowerCase()+", pediu abrigo.","good");
}
function evBirth(){
  const pop=aliveCols().length;
  if(pop>=G.housingCap)return;
  const home=pick(aliveCols().filter(c=>c.home));
  if(!home)return;
  const c=makeColonist(home.x,home.y);
  c.age=0; c.name="Criança "+c.first.split(" ")[0]+" "+home.name.split(" ").slice(-1)[0];
  assignHomes();
  notify("Nascimento","Uma criança nasceu na casa de "+home.first+".","good");
  spawnFloat(home.x+.5,home.y,"♥","#f0788c");
  for(const cc of aliveCols())cc.mood=min(100,cc.mood+5);
}
function evDisease(){
  const cols=aliveCols();
  if(cols.length<2)return;
  const n=min(cols.length-1,randInt(1,Math.max(1,floor(cols.length/3))));
  const inf=G.buildings.some(b=>b&&!b.dead&&b.def==="infirm"&&b.built>=1);
  for(let i=0;i<n;i++){
    const c=pick(cols);
    c.health-=inf?18:38; c.wound="doença";
    c.mood-=12;
    spawnParticle(c.x,c.y,"angry");
  }
  notify("Surto de doença",n+" colono(s) adoeceram"+(inf?" — a enfermaria ajuda.":" — sem enfermaria, é grave."),"bad");
  Audio_.doom();
}
function evBounty(){
  for(const b of G.buildings){
    if(!b||b.dead||b.def!=="farm"||b.built<1)continue;
    if(b.stage>0&&b.stage<4)b.growth=min(1,b.growth+0.3);
  }
  notify("Estação generosa","As plantações tiveram um salto de crescimento.","good");
}
function evWolves(){
  const m=MD();
  const n=clamp(round((1+floor(G.t.day/14))*(m.raid||1)),1,8);
  let any=false;
  for(let i=0;i<n;i++){
    const t=edgeSpawnTile();
    spawnEnemy("wolf",t.x,t.y); any=true;
  }
  if(any){
    banner("ALCATEIA",n+" lobos rondam o vale");
    notify("Lobos à solta",n+" lobos famintos surgiram da floresta.","bad");
    Audio_.doom();
    G.stats.waves++;
  }
}
function evRaid(){
  const m=MD();
  if(!m.raid)return;
  const w=clamp(round(floor(G.threat/9)*m.raid),1,10);
  const hasBoss=w>=4&&chance(.5);
  const t=edgeSpawnTile();
  for(let i=0;i<w;i++){
    const p=edgeSpawnTile();
    spawnEnemy(chance(.25)?"raider":"bandit",clamp(t.x+randInt(-3,3),1,MAP_W-2),clamp(t.y+randInt(-3,3),1,MAP_H-2));
  }
  if(hasBoss)spawnEnemy("raider",t.x,t.y);
  banner("INVASÃO",w+" salteadores atacam a colônia");
  notify("Invasores!",w+" salteadores avançam sobre a colônia. Milicianos, às armas!","bad");
  Audio_.doom();
  G.stats.waves++;
  // militia mobilise
  for(const c of aliveCols())if(c.militia&&c.job){releaseJob(c);}
}

/* ── daily tick ───────────────────────────────────────────────────────── */
function foodPanic(loud){
  const pop=aliveCols().length;
  if(!pop||!G.camp||edible()>=pop*3)return;
  const cand=[];
  for(const n of G.nodes){
    if(!n||n.dead||n.hidden||n.kind!==N.BUSH)continue;
    if(dist(n.x,n.y,G.camp.x,G.camp.y)>34)continue;
    if(G.jobs.some(j=>!j.dead&&j.node===n.id))continue;
    cand.push(n);
  }
  cand.sort((a,b)=>dist2(a.x,a.y,G.camp.x,G.camp.y)-dist2(b.x,b.y,G.camp.x,G.camp.y));
  const want=max(2,ceil(pop*0.5));
  let made=0;
  for(let i=0;i<cand.length&&made<want;i++){
    addJob({type:"gather",x:cand[i].x,y:cand[i].y,node:cand[i].id,prio:18,work:NODEDEF[N.BUSH].work,skill:"farming"});
    made++;
  }
  if(made&&loud)notify("Coleta de emergência","Os colonos buscam bagas silvestres. Plante uma fazenda!","bad");
  if(G.stock.food<pop*1.5){
    for(const a of G.animals){
      if(a.dead||a.kind!=="deer"||a.hunted)continue;
      if(dist(a.x,a.y,G.camp.x,G.camp.y)>32)continue;
      if(G.jobs.some(j=>!j.dead&&j.enemy===a.id))continue;
      a.hunted=true;
      addJob({type:"defend",x:floor(a.x),y:floor(a.y),enemy:a.id,hunt:true,prio:17,work:999,skill:"fighting"});
      break;
    }
  }
}
function haulSweep(){
  if(stockTotal()>=storageCap())return;
  let n=0;
  for(const it of G.items){
    if(n>=6)break;
    if(!it||it.dead)continue;
    if(it.taken){const tc=G.cols[it.taken];if(tc&&tc.alive)continue;it.taken=0;}
    if(G.jobs.some(j=>!j.dead&&j.item===it.id))continue;
    addJob({type:"haul",x:it.x,y:it.y,item:it.id,prio:5,skill:null});
    n++;
  }
}
function dailyTick(){
  const pop=aliveCols().length;
  G.stats.daysSurvived=G.t.day;
  if(_homeRegion&&_homeSize<40){if(!G._sealWarn){G._sealWarn=true;notify("Colônia isolada","Suas construções fecharam a saída — demoli um trecho para reconectar.","bad");}}
  else G._sealWarn=false;
  if(stockTotal()>=storageCap()&&G.items.length>0){
    if(!G._storeWarn){G._storeWarn=true;notify("Depósito cheio","Os materiais estragam no chão — construa um Depósito ou comercialize o excedente.","bad");}
  } else G._storeWarn=false;
  updatePrices(6);
  // caravan departure
  if(G.market.here){G.market.leave--;if(G.market.leave<=0){G.market.here=false;G.market.goods=[];notify("Caravana partiu","Os mercadores seguiram viagem.","info");}}
  // flow decay
  for(const k in G.flow)G.flow[k]*=0.0;
  G.moodShock=max(0,(G.moodShock||0)-3.2);
  // regrowth
  regrowTick();
  // foraging & hunting when food runs short
  foodPanic(true);
  // infirmary tending
  for(const c of G.cols)if(c&&c.alive)c.beingTended=false;
  // population cap / starvation warnings
  if(edible()<=0&&pop>0)notify("Fome!","Não há comida nos armazéns. Os colonos vão adoecer.","bad");
  if(G.season===3&&G.t.day%SEASON_DAYS===0&&!G.buildings.some(b=>b&&!b.dead&&b.def==="house"&&b.built>=1))
    notify("Inverno sem abrigo","Construa casas ou seus colonos morrerão de frio.","bad");
  eventRoll();
  contractTick();
  if(!G.over&&modeWin())gameOver(true);
  // fauna population
  if(G.animals.filter(a=>!a.dead).length<10&&chance(.6)){
    const t=edgeSpawnTile();
    if(G.bio[idx(t.x,t.y)]===B.FOREST||G.bio[idx(t.x,t.y)]===B.MEADOW)spawnAnimal(chance(.4)?"deer":"rabbit",t.x,t.y);
  }
  autosave();
  // yearly summary
  if(G.t.day>0&&G.t.day%(SEASON_DAYS*4)===0){
    banner("ANO "+G.year,"a colônia resistiu");
    notify("Ano "+G.year+" completo",pop+" colonos sobrevivem. Riqueza: "+fmt(wealth())+".","epic");
    addPrestige(1,"Mais um ano de colônia registrada nos anais");
  }
}
function regrowTick(){
  let trees=0;
  for(let i=0;i<G.nodes.length;i++){
    const n=G.nodes[i];
    if(!n||n.dead)continue;
    if(n.kind<=3||n.kind===8)trees++;
    if(n.hidden&&n.regrowT!==undefined){
      n.regrowT--;
      if(n.regrowT<=0){
        n.hidden=false; n.amount=n.max; n.growth=0.25;
        recomputeCostLocal(n.x,n.y);
      }
    }
  }
  // saplings in forest
  const cap=Math.round(MAP_W*MAP_H*0.13);
  if(trees<cap){
    for(let t=0;t<26;t++){
      const x=randInt(2,MAP_W-3),y=randInt(2,MAP_H-3),i=idx(x,y);
      if(G.bio[i]!==B.FOREST||G.res[i]||G.bld[i]||!BPASS[G.bio[i]])continue;
      const kind=(G.hgt[i]>3||chance(.45))?N.PINE:(chance(.6)?N.OAK:N.BIRCH);
      const n=addNode(kind,x,y);
      n.growth=0.18; n.scale=0.4;
      break;
    }
  }
}

/* ── main simulation tick ─────────────────────────────────────────────── */
let _dailyAcc=0, _lastDay=-1;
function simulate(dt){
  // clock
  G.t.min+=dt*MIN_PER_SEC;
  const nd=floor(G.t.min/DAY_MIN);
  if(nd!==_lastDay){_lastDay=nd;G.t.day=nd;}
  G.season=floor(G.t.day/SEASON_DAYS)%4;
  G.seasonDay=G.t.day%SEASON_DAYS;
  G.year=floor(G.t.day/(SEASON_DAYS*4))+1;
  G.temp=tempNow();

  // season change banner
  const sd=G.t.day;
  if(sd!==G._lastSeasonDay){
    if(G._lastSeasonDay!==undefined&&sd%SEASON_DAYS===0){
      const S=SEASONS[G.season];
      banner(S.name.toUpperCase(),"ano "+G.year+" · "+S.desc);
      notify("Nova estação: "+S.name,S.desc,"info");
      Audio_.bell();
      if(G.season===0){for(const b of G.buildings)if(b&&!b.dead&&b.def==="farm"&&b.built>=1){b.tilled=false;b.stage=0;b.growth=0;}}
    }
    G._lastSeasonDay=sd;
  }
  if(sd!==G._lastDaily&&G._lastDaily!==undefined){dailyTick();}
  G._lastDaily=sd;

  weatherTick(dt);
  fireTick(dt);
  G._panicT=(G._panicT||0)-dt*MIN_PER_SEC;
  if(G._panicT<=0){G._panicT=110;foodPanic(false);haulSweep();}

  // buildings
  for(const b of G.buildings){
    if(!b||b.dead)continue;
    if(b.built>=1){
      if(b.def==="farm"||b.def==="orchard")farmTick(b,dt);
      else if(BDEF[b.def].craft||b.def==="mine"||b.def==="market")craftTick(b,dt);
      else if(b.def==="academy"||b.def==="garrison")schoolTick(b,dt);
      // chimney smoke
      if((b.def==="house"||b.def==="workshop"||b.def==="bakery")&&chance(dt*(isNight()?2.6:1.4)))
        spawnParticle(b.x+b.w*0.62,b.y+b.h*0.35,"smoke");
    }
    b.anim+=dt;
  }

  // colonists
  for(const c of G.cols)if(c&&c.alive)updateColonist(c,dt);

  // enemies / fauna
  for(const e of G.enemies)if(e&&!e.dead)updateEnemy(e,dt);
  for(const a of G.animals)if(a&&!a.dead)updateAnimal(a,dt);

  // ambience particles
  if(G.season===0&&chance(dt*3))spawnParticle(camTileX()+rand(-14,14),camTileY()+rand(-9,9),"petal");
  if(G.wx.type==="rain"&&chance(dt*26))spawnParticle(camTileX()+rand(-16,16),camTileY()+rand(-10,10),"drop");
  if(G.wx.type==="snow"&&chance(dt*18))spawnParticle(camTileX()+rand(-16,16),camTileY()+rand(-10,10),"snowp");

  updateParticles(dt);
  itemAging(dt);
  if(G.buff.festival>0){G.buff.festival-=dt*MIN_PER_SEC;if(G.buff.festival<=0){G.buff.festival=0;notify("Fim do festival","A colônia volta à rotina.","info");}}

  // compaction
  if(chance(dt*0.12))compact();

  // defeat
  if(aliveCols().length===0&&!G.over&&G.t.day>0)gameOver(false);
}
function compact(){
  G.items=G.items.filter(i=>i&&!i.dead);
  G.enemies=G.enemies.filter(e=>e&&!e.dead);
  G.animals=G.animals.filter(a=>a&&!a.dead);
  G.jobs=G.jobs.filter(j=>j&&!j.dead);
  // clear stale reservations
  for(const j of G.jobs){
    if(!j.by)continue;
    const c=G.cols[j.by];
    if(!c||!c.alive||c.job!==j)j.by=0;
  }
  if(G.items.length>400)G.items.splice(0,G.items.length-400);
}
function camTileX(){return G.cam.tx;} function camTileY(){return G.cam.ty;}

function gameOver(won){
  G.over=true; G.t.paused=true; G.t.speed=0; syncSpeedUI();
  updateGoalBar();
  try{localStorage.removeItem(SAVE_KEY);}catch(e){}
  $("#btnContinue").disabled=true;
  const m=MD();
  const ep=won?(m.policy==="chain"?"A escritura do vale é sua.":(m.win&&m.win.coin?"A fortuna está contada no cofre.":"O vale resistiu ao que veio."))
              :"O vale segue sem seus colonos.";
  openModal({
    title:won?"A colônia prospera":"A colônia pereceu",
    sub:m.name+" · "+ep,
    body:`<div class="stat"><span>Modo</span><b>${m.name}</b></div>
      <div class="stat"><span>Dias sobrevividos</span><b>${G.t.day}</b></div>
      <div class="stat"><span>Pico populacional</span><b>${G.popPeak}</b></div>
      <div class="stat"><span>Contratos cumpridos</span><b>${G.stats.contracts}</b></div>
      <div class="stat"><span>Prestígio ganho</span><b>${G.prestigeEarned||0}</b></div>
      <div class="stat"><span>Construções erguidas</span><b>${G.stats.built}</b></div>
      <div class="stat"><span>Colheitas</span><b>${G.stats.harvested}</b></div>
      <div class="stat"><span>Invasões repelidas</span><b>${G.stats.waves}</b></div>
      <div class="stat"><span>Mortes</span><b>${G.stats.died}</b></div>
      <div class="stat"><span>Riqueza final</span><b>${fmt(wealth())}</b></div>`,
    foot:[{label:"Recomeçar",cls:"pri",fn:()=>{closeModal();showTitle();}}],
    dismissable:false
  });
  won?Audio_.fanfare():Audio_.doom();
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 8 · renderer — camera, terrain, water, seasons
═══════════════════════════════════════════════════════════════════════════════*/

const HW=TW*0.5, HH=TH*0.5;
const isoX=(x,y)=>(x-y)*HW;
const isoY=(x,y)=>(x+y)*HH;
function toScreen(x,y){const z=G.cam.z;return{x:isoX(x,y)*z+VW*0.5+G.cam.x, y:isoY(x,y)*z+VH*0.5+G.cam.y};}
function toTile(mx,my){
  const z=G.cam.z;
  const ux=(mx-VW*0.5-G.cam.x)/z, uy=(my-VH*0.5-G.cam.y)/z;
  return {x:(ux/HW+uy/HH)*0.5, y:(uy/HH-ux/HW)*0.5};
}
let LIGHT_CV=null,LCTX=null,FOG_CV=null,FCTX=null;
function initVisual(){
  G.tv=new Float32Array(MAP_W*MAP_H);
  const pn=new Perlin(hashStr(String(G.seed))^0x77aa11);
  const pn2=new Perlin(hashStr(String(G.seed))^0x1234);
  for(let y=0;y<MAP_H;y++)for(let x=0;x<MAP_W;x++){
    const i=y*MAP_W+x;
    G.tv[i]=pn.noise2(x*0.31,y*0.31)*0.55 + pn2.noise2(x*1.7,y*1.7)*0.45;
  }
  LIGHT_CV=document.createElement("canvas"); LCTX=LIGHT_CV.getContext("2d");
  FOG_CV=document.createElement("canvas"); FCTX=FOG_CV.getContext("2d");
  buildMinimapBase();
}
function resizeLight(){
  if(!LIGHT_CV)return;
  const s=0.5;
  LIGHT_CV.width=max(2,round(VW*s)); LIGHT_CV.height=max(2,round(VH*s));
  FOG_CV.width=max(2,round(VW*0.34)); FOG_CV.height=max(2,round(VH*0.34));
}
window.addEventListener("resize",resizeLight);

/* season-blended terrain palette, recomputed once per frame */
let PAL=[], SNOW=0, WIND=0, VEG=[], VEG2=[];
const VEG_SEASON=[
  /*spring*/[[[96,158,86],[62,118,58],[150,196,110]],[[70,132,80],[44,98,58],[120,176,110]]],
  /*summer*/[[[74,140,62],[46,102,44],[132,182,92]],[[52,116,62],[32,86,48],[102,160,86]]],
  /*autumn*/[[[196,132,54],[150,88,40],[232,178,86]],[[178,104,48],[126,64,34],[216,150,74]]],
  /*winter*/[[[176,182,186],[128,136,144],[222,228,234]],[[120,124,120],[84,90,88],[176,184,188]]],
];
function updatePalette(){
  const S=G.season, nx=(S+1)%4;
  const bl=smooth(sat((G.seasonDay-(SEASON_DAYS-4))/4));
  PAL=[];
  for(let b=0;b<BIOME_COL.length;b++)PAL.push(mixRGB(BIOME_COL[b][S],BIOME_COL[b][nx],bl));
  VEG=[];VEG2=[];
  for(let v=0;v<2;v++)for(let c=0;c<3;c++){
    const a=VEG_SEASON[S][v][c], b2=VEG_SEASON[nx][v][c];
    (v?VEG2:VEG).push(mixRGB(a,b2,bl));
  }
  const want=(G.season===3)?1:(G.season===0?max(0,1-G.seasonDay/4):0);
  SNOW+=(want-SNOW)*0.02;
  WIND=Math.sin(G.t.elapsed*0.21)*0.55+Math.sin(G.t.elapsed*0.53+1.7)*0.35+Math.sin(G.t.elapsed*1.31)*0.12;
  if(G.wx.type==="storm")WIND*=2.6; else if(G.wx.type==="rain")WIND*=1.5;
}

/* sky / ambient light curve */
function skyTop(){
  const h=(G.t.min/60)%24, L=dayLight();
  const night=[8,11,22], dawn=[64,54,86], day=[126,168,206];
  let c;
  if(h<4.5||h>20.5)c=night;
  else if(h<7)c=mixRGB(night,dawn,smooth(sat((h-4.5)/2.5)));
  else if(h<9)c=mixRGB(dawn,day,smooth(sat((h-7)/2)));
  else if(h<17.5)c=day;
  else if(h<19.5)c=mixRGB(day,dawn,smooth(sat((h-17.5)/2)));
  else c=mixRGB(dawn,night,smooth(sat((h-19.5)/1)));
  return mixRGB(c,[42,52,72],1-L);
}
function ambience(){
  const L=dayLight();
  const h=(G.t.min/60)%24;
  // warm at dawn/dusk, cool at night, neutral midday
  let warm=0;
  if(h>5&&h<8.5)warm=1-smooth(sat((h-5)/3.5));
  if(h>17&&h<20.5)warm=smooth(sat((h-17)/2))*(1-smooth(sat((h-19.2)/1.3)));
  return {L,warm,night:1-L};
}

/* ── terrain pass ─────────────────────────────────────────────────────── */
function visibleRange(){
  const cs=[[0,0],[VW,0],[0,VH],[VW,VH]];
  let x0=1e9,x1=-1e9,y0=1e9,y1=-1e9;
  for(const c of cs){
    const t=toTile(c[0],c[1]);
    x0=min(x0,floor(t.x));x1=max(x1,ceil(t.x));
    y0=min(y0,floor(t.y));y1=max(y1,ceil(t.y));
  }
  // the tile-space box is ~2× the on-screen diamond, so also carry a world-space
  // clip rect (screen space is axis-aligned) to reject the corners cheaply
  const z=G.cam.z||1, ox=VW*0.5+G.cam.x, oy=VH*0.5+G.cam.y;
  return {x0:clamp(x0-2,-1,MAP_W),x1:clamp(x1+3,0,MAP_W+1),y0:clamp(y0-2,-1,MAP_H),y1:clamp(y1+3,0,MAP_H+1),
    wx0:(0-ox)/z-HW*1.6, wx1:(VW-ox)/z+HW*1.6, wy0:(0-oy)/z-TH*2.2, wy1:(VH-oy)/z+TH*2.2};
}

function diamondPath(px,py){
  ctx.beginPath();
  ctx.moveTo(px,py-TH*0.5);
  ctx.lineTo(px+HW,py);
  ctx.lineTo(px,py+TH*0.5);
  ctx.lineTo(px-HW,py);
  ctx.closePath();
}

function drawTerrain(vr,time){
  const A=ambience();
  const waterShift=(G.wx.type==="storm")?1.5:(G.wx.type==="rain")?0.9:0.35;
  const amb=0.34+A.L*0.74;
  const warmR=A.warm*26, warmG=A.warm*8, warmB=-A.warm*10;
  const nOn=A.night>0.35, nR=nOn?-A.night*7:0, nB=nOn?A.night*17:0;
  const wf=0.96+A.L*0.1, wfB=1.0+A.L*0.08;
  const relief=css([0,0,0],0.10);
  const wx0=vr.wx0,wx1=vr.wx1,wy0=vr.wy0,wy1=vr.wy1;
  for(let y=vr.y0;y<vr.y1;y++){
    for(let x=vr.x0;x<vr.x1;x++){
      if(x<0||y<0||x>=MAP_W||y>=MAP_H)continue;
      const i=y*MAP_W+x;
      const b=G.bio[i];
      const px=isoX(x,y);
      if(px<wx0||px>wx1)continue;
      const cy=isoY(x,y);
      if(cy<wy0||cy>wy1)continue;
      const P=PAL[b];
      const h=G.hgt[i];
      const hf=h>0?1+h*0.045:1;
      const v=G.tv[i];
      let r=(P[0]*hf+v*13)*amb+warmR+nR;
      let g=(P[1]*hf+v*15)*amb+warmG;
      let bl=(P[2]*hf+v*9)*amb+warmB+nB;
      const isW=b===B.WATER||b===B.DEEP;
      if(isW){
        const w=Math.sin(time*1.5*waterShift+(x*0.42+y*0.31))*0.5+Math.sin(time*2.3*waterShift+(x*0.19-y*0.47))*0.5;
        r=(r+w*10)*wf; g=(g+w*14)*wf; bl=(bl+w*22)*wfB;
      }
      ctx.fillStyle=css([r,g,bl]);
      diamondPath(px,cy);
      ctx.fill();

      // water surface detail + shoreline foam
      if(isW){
        const sp=Math.sin(time*2.1+(x*1.7+y*2.3))*0.5+0.5;
        if(sp>0.86){
          ctx.strokeStyle=css([255,255,255],0.10*A.L+0.02);
          ctx.lineWidth=1.1;
          ctx.beginPath();
          ctx.moveTo(px-HW*0.42,cy+1.5);ctx.lineTo(px-HW*0.05,cy+3.2);
          ctx.stroke();
        }
        // foam where adjacent to land
        let landN=0;
        if(y>0&&BPASS[G.bio[i-MAP_W]]&&G.bio[i-MAP_W]!==B.WATER&&G.bio[i-MAP_W]!==B.DEEP)landN|=1;
        if(x<MAP_W-1&&BPASS[G.bio[i+1]]&&G.bio[i+1]!==B.WATER&&G.bio[i+1]!==B.DEEP)landN|=2;
        if(y<MAP_H-1&&BPASS[G.bio[i+MAP_W]]&&G.bio[i+MAP_W]!==B.WATER&&G.bio[i+MAP_W]!==B.DEEP)landN|=4;
        if(x>0&&BPASS[G.bio[i-1]]&&G.bio[i-1]!==B.WATER&&G.bio[i-1]!==B.DEEP)landN|=8;
        if(landN){
          const fo=0.16+Math.sin(time*1.7+x*0.8+y*0.6)*0.07;
          ctx.fillStyle=css([236,248,255],fo*(0.35+A.L*0.65));
          diamondPath(px,cy);ctx.fill();
        }
      }
      // subtle inner edge for relief on high ground
      if(h>=3&&!isW){
        ctx.strokeStyle=relief;ctx.lineWidth=1;
        diamondPath(px,cy);ctx.stroke();
      }
    }
  }
}

/* ── overlay: roads, farmland, snow, fire scars ───────────────────────── */
function drawOverlay(vr,time){
  const A=ambience();
  const amb=0.36+A.L*0.72;
  const wx0=vr.wx0,wx1=vr.wx1,wy0=vr.wy0,wy1=vr.wy1;
  for(let y=vr.y0;y<vr.y1;y++)for(let x=vr.x0;x<vr.x1;x++){
    if(x<0||y<0||x>=MAP_W||y>=MAP_H)continue;
    const i=y*MAP_W+x;
    const o=G.ovr[i];
    if(!o)continue;
    const px=isoX(x,y);
    if(px<wx0||px>wx1)continue;
    const cy=isoY(x,y);
    if(cy<wy0||cy>wy1)continue;
    if(o===O.ROAD){
      ctx.fillStyle=css(shade([150,132,104],amb));
      diamondPath(px,cy);ctx.fill();
      // connect to neighbours
      ctx.strokeStyle=css(shade([168,150,120],amb));ctx.lineWidth=TH*0.42;ctx.lineCap="round";
      const nb=[[1,0],[-1,0],[0,1],[0,-1]];
      for(const d of nb){
        const j=(y+d[1])*MAP_W+(x+d[0]);
        if(!inb(x+d[0],y+d[1]))continue;
        if(G.ovr[j]===O.ROAD||G.bld[j]){
          ctx.beginPath();ctx.moveTo(px,cy);ctx.lineTo(px+d[0]*HW-d[1]*HW,cy+d[0]*HH+d[1]*HH);ctx.stroke();
        }
      }
      ctx.lineWidth=1;
      // gravel speckle
      const hsh=(x*73856093^y*19349663)>>>0;
      ctx.fillStyle=css(shade([126,110,88],amb),.7);
      for(let k=0;k<3;k++){
        const a=(hsh>>>(k*5))%17/17*TAU, r=((hsh>>>(k*3+2))%11)/11*HW*0.55;
        ctx.fillRect(px+Math.cos(a)*r-1,cy+Math.sin(a)*r*0.5-1,2,1.6);
      }
    } else if(o===O.FARM){
      const b=G.buildings[G.bld[i]];
      const fer=G.fer[i]/100;
      const soil=mixRGB([96,64,42],[128,92,58],fer);
      ctx.fillStyle=css(shade(soil,amb));
      diamondPath(px,cy);ctx.fill();
      // furrows
      ctx.strokeStyle=css(shade([62,40,26],amb),.55);ctx.lineWidth=1.1;
      ctx.beginPath();ctx.moveTo(px-HW*0.5,cy-HH*0.25);ctx.lineTo(px+HW*0.5,cy+HH*0.25);ctx.stroke();
      if(b&&b.stage>0)drawCropTile(px,cy,b,x,y,time,amb);
    }
    // scorched ground
    if(G.fire[i]>0){
      ctx.fillStyle=css([26,18,14],0.30);diamondPath(px,cy);ctx.fill();
    }
  }
}
function drawCropTile(px,cy,b,x,y,time,amb){
  const cd=CROPS[b.crop]; if(!cd)return;
  const st=b.stage, g=b.growth;
  const late=(st>=3);
  const c0=hex2rgb(cd.col[late?1:0][0]), c1=hex2rgb(cd.col[late?1:0][1]);
  const hh=(st===1?2.2:st===2?4.6:st===3?7.4:9.6);
  const sway=WIND*(b.crop==="flax"?2.6:1.5);
  for(let k=0;k<3;k++){
    const ox=(k-1)*HW*0.42;
    const oy=(k-1)*HH*0.21;
    const sw=Math.sin(time*2.1+x*0.7+y*0.5+k)*sway;
    ctx.strokeStyle=css(shade(mixRGB(c0,c1,k/3),amb*(0.85+st*0.06)));
    ctx.lineWidth=st>=3?1.8:1.2;
    ctx.beginPath();
    ctx.moveTo(px+ox,cy+oy);
    ctx.quadraticCurveTo(px+ox+sw*0.5,cy+oy-hh*0.6,px+ox+sw,cy+oy-hh);
    ctx.stroke();
    if(st>=3){
      ctx.fillStyle=css(shade(c1,amb*1.12));
      ctx.beginPath();ctx.ellipse(px+ox+sw,cy+oy-hh,1.9,2.9,0,0,TAU);ctx.fill();
    }
  }
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 9 · sprites — vegetation, rocks, buildings
═══════════════════════════════════════════════════════════════════════════════*/

let AMB=1,WARM=0,NIGHT=0;
const _lc=[0,0,0],_lc2=[0,0,0];
function L(c,f){
  const m=AMB*(f===undefined?1:f);
  _lc[0]=clamp(c[0]*m+WARM*24,0,255);
  _lc[1]=clamp(c[1]*m+WARM*7,0,255);
  _lc[2]=clamp(c[2]*m-WARM*9+(NIGHT>0.3?NIGHT*15:0),0,255);
  return css(_lc);
}
function L2(c,f){
  const m=AMB*(f===undefined?1:f);
  _lc2[0]=clamp(c[0]*m+WARM*24,0,255);
  _lc2[1]=clamp(c[1]*m+WARM*7,0,255);
  _lc2[2]=clamp(c[2]*m-WARM*9+(NIGHT>0.3?NIGHT*15:0),0,255);
  return css(_lc2);
}
function shadow(px,py,rx,ry,a){
  ctx.fillStyle=css([10,14,10],a===undefined?0.30*AMB:a);
  ctx.beginPath();ctx.ellipse(px+rx*0.22,py+ry*0.18,rx,ry,0,0,TAU);ctx.fill();
}

/* ── vegetation ───────────────────────────────────────────────────────── */
function drawTree(px,py,n,time){
  const d=NODEDEF[n.kind];
  const g=n.growth===undefined?1:n.growth;
  const s=n.scale*(0.35+g*0.65);
  const h=d.h*s;
  const sway=WIND*d.sway*s*3.2+Math.sin(time*1.7+n.seed)*0.7*s;
  const bare=(n.kind===N.OAK||n.kind===N.BIRCH)&&SNOW>0.42;
  shadow(px,py,13*s,5.2*s,0.30*AMB);
  const vset=(n.variant===0?VEG:(n.variant===1?VEG2:VEG));
  const cDark=vset[1],cMid=vset[0],cLit=vset[2];

  if(n.kind===N.PINE){
    // trunk
    ctx.strokeStyle=L([74,50,32]);ctx.lineWidth=max(1.6,3.1*s);ctx.lineCap="round";
    ctx.beginPath();ctx.moveTo(px,py);ctx.lineTo(px+sway*0.55,py-h*0.62);ctx.stroke();
    const layers=4;
    for(let k=layers-1;k>=0;k--){
      const t=k/(layers-1);
      const yy=py-h*0.28-t*h*0.72;
      const w=(11.5-t*7.6)*s;
      const hh=(12.5-t*3.4)*s;
      const xx=px+sway*(0.3+t*0.7);
      ctx.fillStyle=L(cDark,0.86+t*0.1);
      ctx.beginPath();ctx.moveTo(xx-w,yy);ctx.lineTo(xx+w,yy);ctx.lineTo(xx,yy-hh);ctx.closePath();ctx.fill();
      ctx.fillStyle=L(cMid,0.94+t*0.12);
      ctx.beginPath();ctx.moveTo(xx-w*0.82,yy-hh*0.16);ctx.lineTo(xx+w*0.5,yy-hh*0.2);ctx.lineTo(xx,yy-hh);ctx.closePath();ctx.fill();
      if(SNOW>0.05){
        ctx.fillStyle=css([238,246,255],SNOW*0.82*AMB+0.1);
        ctx.beginPath();ctx.moveTo(xx-w*0.66,yy-hh*0.32);ctx.lineTo(xx+w*0.4,yy-hh*0.36);ctx.lineTo(xx,yy-hh);ctx.closePath();ctx.fill();
      }
    }
  } else if(bare){
    ctx.strokeStyle=L(n.kind===N.BIRCH?[214,208,196]:[78,54,34]);
    ctx.lineCap="round";
    ctx.lineWidth=max(1.8,3.6*s);
    ctx.beginPath();ctx.moveTo(px,py);ctx.lineTo(px+sway*0.5,py-h*0.62);ctx.stroke();
    ctx.lineWidth=max(1,2*s);
    for(let k=0;k<6;k++){
      const a=-PI*0.5+(k/5-0.5)*2.1, t=0.42+k*0.09;
      const bx=px+sway*t*0.5, by=py-h*t;
      ctx.strokeStyle=L(n.kind===N.BIRCH?[206,200,190]:[70,48,30],0.92);
      ctx.beginPath();ctx.moveTo(bx,by);
      ctx.quadraticCurveTo(bx+Math.cos(a)*9*s,by+Math.sin(a)*9*s-h*0.09,bx+Math.cos(a)*15*s+sway,by+Math.sin(a)*15*s-h*0.16);
      ctx.stroke();
    }
    if(SNOW>0.1){
      ctx.fillStyle=css([240,247,255],SNOW*0.7);
      for(let k=0;k<4;k++){const a=k*1.7+n.seed;ctx.beginPath();ctx.ellipse(px+Math.cos(a)*8*s,py-h*0.72+Math.sin(a)*5*s,3.4*s,1.5*s,0,0,TAU);ctx.fill();}
    }
  } else {
    // trunk
    ctx.strokeStyle=L(n.kind===N.BIRCH?[222,216,204]:[80,54,34]);
    ctx.lineCap="round";ctx.lineWidth=max(1.8,(n.kind===N.BIRCH?2.6:3.8)*s);
    ctx.beginPath();ctx.moveTo(px,py);
    ctx.quadraticCurveTo(px+sway*0.28,py-h*0.36,px+sway*0.55,py-h*0.58);ctx.stroke();
    if(n.kind===N.BIRCH){
      ctx.strokeStyle=L([60,50,44],.8);ctx.lineWidth=max(.6,1*s);
      for(let k=0;k<3;k++){const yy=py-h*(0.12+k*0.14);ctx.beginPath();ctx.moveTo(px-1.6*s+sway*0.2,yy);ctx.lineTo(px+1.6*s+sway*0.2,yy);ctx.stroke();}
    }
    // canopy
    const cx=px+sway, cy=py-h*0.78;
    const R=(n.kind===N.OAK?13.5:11)*s;
    const blobs=[[0,0,1.0],[-0.72,0.24,0.74],[0.74,0.2,0.72],[-0.24,-0.62,0.7],[0.4,-0.5,0.6]];
    for(let k=0;k<blobs.length;k++){
      const bl=blobs[k];
      ctx.fillStyle=L(cDark,0.82);
      ctx.beginPath();ctx.arc(cx+bl[0]*R,cy+bl[1]*R+R*0.16,R*bl[2],0,TAU);ctx.fill();
    }
    for(let k=0;k<blobs.length;k++){
      const bl=blobs[k];
      ctx.fillStyle=L(k<2?cMid:cMid,0.98);
      ctx.beginPath();ctx.arc(cx+bl[0]*R,cy+bl[1]*R,R*bl[2]*0.93,0,TAU);ctx.fill();
    }
    // sun highlight (upper-left)
    ctx.fillStyle=L(cLit,1.06);
    ctx.beginPath();ctx.arc(cx-R*0.42,cy-R*0.46,R*0.52,0,TAU);ctx.fill();
    ctx.fillStyle=css([255,255,255],0.055*AMB);
    ctx.beginPath();ctx.arc(cx-R*0.52,cy-R*0.58,R*0.28,0,TAU);ctx.fill();
    // fruit on orchard-ish oaks in autumn
    if(G.season===2&&n.kind===N.OAK&&n.variant===2){
      ctx.fillStyle=L([206,72,54]);
      for(let k=0;k<4;k++){const a=k*1.9+n.seed;ctx.beginPath();ctx.arc(cx+Math.cos(a)*R*0.6,cy+Math.sin(a)*R*0.5,1.7*s,0,TAU);ctx.fill();}
    }
    if(SNOW>0.05){
      ctx.fillStyle=css([240,247,255],SNOW*0.55*AMB);
      ctx.beginPath();ctx.arc(cx-R*0.2,cy-R*0.5,R*0.7,PI,TAU);ctx.fill();
    }
  }
}
function drawRock(px,py,n,time){
  const s=n.scale*(0.7+(n.growth===undefined?1:n.growth)*0.3);
  const ore=n.kind===N.ORE;
  shadow(px,py,12*s,4.6*s,0.32*AMB);
  const base=ore?[92,92,102]:[132,132,140];
  const pts=[[0,-16*s],[-11*s,-6*s],[-7*s,3*s],[6*s,4*s],[12*s,-5*s],[5*s,-13*s]];
  ctx.fillStyle=L(shade(base,0.72));
  ctx.beginPath();ctx.moveTo(px+pts[0][0],py+pts[0][1]);
  for(let k=1;k<pts.length;k++)ctx.lineTo(px+pts[k][0],py+pts[k][1]);
  ctx.closePath();ctx.fill();
  // lit top-left facet
  ctx.fillStyle=L(shade(base,1.08));
  ctx.beginPath();ctx.moveTo(px+pts[0][0],py+pts[0][1]);ctx.lineTo(px+pts[1][0],py+pts[1][1]);
  ctx.lineTo(px+pts[2][0]*0.2,py+pts[2][1]*0.4);ctx.lineTo(px+pts[5][0],py+pts[5][1]);ctx.closePath();ctx.fill();
  ctx.fillStyle=L(shade(base,0.86));
  ctx.beginPath();ctx.moveTo(px+pts[0][0],py+pts[0][1]);ctx.lineTo(px+pts[5][0],py+pts[5][1]);
  ctx.lineTo(px+pts[4][0],py+pts[4][1]);ctx.closePath();ctx.fill();
  if(ore){
    for(let k=0;k<5;k++){
      const a=n.seed+k*2.3, r=6*s;
      const gl=0.6+Math.sin(time*2.2+k*1.7)*0.4;
      ctx.fillStyle=css([246,206,120],(0.35+gl*0.45)*AMB);
      ctx.beginPath();ctx.arc(px+Math.cos(a)*r,py-8*s+Math.sin(a)*r*0.45,1.5*s+gl*0.5,0,TAU);ctx.fill();
    }
  }
  if(SNOW>0.3){ctx.fillStyle=css([240,247,255],SNOW*0.6*AMB);
    ctx.beginPath();ctx.ellipse(px,py-14*s,7*s,3*s,0,0,TAU);ctx.fill();}
}
function drawBush(px,py,n,time){
  const s=n.scale;
  const has=n.amount>0&&!n.hidden;
  shadow(px,py,8*s,3.2*s,0.24*AMB);
  const sw=Math.sin(time*2.4+n.seed)*WIND*2.4*s;
  const g=SNOW>0.4?[128,140,124]:VEG[1];
  for(let k=0;k<3;k++){
    ctx.fillStyle=L(shade(g,0.82+k*0.12));
    ctx.beginPath();ctx.arc(px+(k-1)*4.6*s+sw,py-4.5*s-(k===1?2.2*s:0),5.6*s,0,TAU);ctx.fill();
  }
  if(has){
    ctx.fillStyle=L([196,54,64]);
    for(let k=0;k<5;k++){const a=n.seed+k*1.25;
      ctx.beginPath();ctx.arc(px+Math.cos(a)*5.4*s+sw,py-5.5*s+Math.sin(a)*3.2*s,1.5*s,0,TAU);ctx.fill();}
  }
  if(SNOW>0.3){ctx.fillStyle=css([240,247,255],SNOW*0.55*AMB);
    ctx.beginPath();ctx.ellipse(px+sw,py-8.4*s,6*s,2.4*s,0,0,TAU);ctx.fill();}
}
function drawFlax(px,py,n,time){
  const s=n.scale;
  const sw=Math.sin(time*2.8+n.seed)*WIND*3.2*s;
  const dry=G.season>=2;
  for(let k=0;k<6;k++){
    const ox=(k-2.5)*2.1*s;
    ctx.strokeStyle=L(dry?[176,162,110]:[104,140,82],0.95);
    ctx.lineWidth=1.1;
    ctx.beginPath();ctx.moveTo(px+ox,py);
    ctx.quadraticCurveTo(px+ox+sw*0.5,py-7*s,px+ox+sw,py-13*s);ctx.stroke();
    if(n.amount>0){
      ctx.fillStyle=L(dry?[206,186,226]:[150,168,226]);
      ctx.beginPath();ctx.arc(px+ox+sw,py-13.4*s,1.5*s,0,TAU);ctx.fill();
    }
  }
}
function drawNode(px,py,n,time){
  if(n.hidden)return;
  switch(n.kind){
    case N.OAK:case N.PINE:case N.BIRCH:case N.DEADTREE:drawTree(px,py,n,time);break;
    case N.BOULDER:case N.ORE:drawRock(px,py,n,time);break;
    case N.BUSH:drawBush(px,py,n,time);break;
    case N.FLAX:drawFlax(px,py,n,time);break;
  }
  if(n.marked){
    const t=time*3;
    ctx.strokeStyle=css([255,220,140],0.55+Math.sin(t)*0.25);
    ctx.lineWidth=1.6;
    ctx.beginPath();ctx.ellipse(px,py,13,6,0,0,TAU);ctx.stroke();
  }
}

/* ── isometric primitives ─────────────────────────────────────────────── */
function isoBox(x0,y0,x1,y1,h,top,left,right){
  const ax=isoX(x0,y0),ay=isoY(x0,y0);
  const bx=isoX(x1,y0),by=isoY(x1,y0);
  const cx=isoX(x1,y1),cy=isoY(x1,y1);
  const dx=isoX(x0,y1),dy=isoY(x0,y1);
  ctx.fillStyle=left;ctx.beginPath();ctx.moveTo(dx,dy);ctx.lineTo(cx,cy);ctx.lineTo(cx,cy-h);ctx.lineTo(dx,dy-h);ctx.closePath();ctx.fill();
  ctx.fillStyle=right;ctx.beginPath();ctx.moveTo(cx,cy);ctx.lineTo(bx,by);ctx.lineTo(bx,by-h);ctx.lineTo(cx,cy-h);ctx.closePath();ctx.fill();
  ctx.fillStyle=top;ctx.beginPath();ctx.moveTo(ax,ay-h);ctx.lineTo(bx,by-h);ctx.lineTo(cx,cy-h);ctx.lineTo(dx,dy-h);ctx.closePath();ctx.fill();
}
function gableRoof(x0,y0,x1,y1,wh,rh,colFront,colSide,ov){
  ov=ov||0.14;
  const X0=x0-ov,X1=x1+ov,Y0=y0-ov,Y1=y1+ov,YM=(y0+y1)*0.5;
  const f=[[X0,Y1],[X1,Y1],[X1,YM],[X0,YM]];
  ctx.fillStyle=colFront;
  ctx.beginPath();
  ctx.moveTo(isoX(f[0][0],f[0][1]),isoY(f[0][0],f[0][1])-wh);
  for(let k=1;k<4;k++)ctx.lineTo(isoX(f[k][0],f[k][1]),isoY(f[k][0],f[k][1])-wh);
  ctx.lineTo(isoX(X1,YM),isoY(X1,YM)-wh-rh);
  ctx.lineTo(isoX(X0,YM),isoY(X0,YM)-wh-rh);
  ctx.closePath();ctx.fill();
  ctx.fillStyle=colSide;
  ctx.beginPath();
  ctx.moveTo(isoX(X1,Y0),isoY(X1,Y0)-wh);
  ctx.lineTo(isoX(X1,Y1),isoY(X1,Y1)-wh);
  ctx.lineTo(isoX(X1,YM),isoY(X1,YM)-wh-rh);
  ctx.closePath();ctx.fill();
  // ridge highlight
  ctx.strokeStyle=css([255,255,255],0.13*AMB);ctx.lineWidth=1.4;
  ctx.beginPath();ctx.moveTo(isoX(X0,YM),isoY(X0,YM)-wh-rh);ctx.lineTo(isoX(X1,YM),isoY(X1,YM)-wh-rh);ctx.stroke();
  if(SNOW>0.25){
    ctx.fillStyle=css([240,247,255],SNOW*0.62*AMB);
    ctx.beginPath();
    ctx.moveTo(isoX(X0,YM),isoY(X0,YM)-wh-rh);
    ctx.lineTo(isoX(X1,YM),isoY(X1,YM)-wh-rh);
    ctx.lineTo(isoX(X1,Y1*0.72+YM*0.28),isoY(X1,Y1*0.72+YM*0.28)-wh-rh*0.55);
    ctx.lineTo(isoX(X0,Y1*0.72+YM*0.28),isoY(X0,Y1*0.72+YM*0.28)-wh-rh*0.55);
    ctx.closePath();ctx.fill();
  }
}
function drawProgress(b,px,py){
  const w=34,h=4.5;
  ctx.fillStyle=css([0,0,0],0.55);
  ctx.fillRect(px-w/2-1,py-w*0.02-h/2-1,w+2,h+2);
  ctx.fillStyle=css([70,84,102]);ctx.fillRect(px-w/2,py-h/2,w,h);
  const g=ctx.createLinearGradient(px-w/2,0,px-w/2+w*b.built,0);
  g.addColorStop(0,"#ffd694");g.addColorStop(1,"#e0a145");
  ctx.fillStyle=g;ctx.fillRect(px-w/2,py-h/2,w*clamp(b.built,0,1),h);
  ctx.strokeStyle=css([255,255,255],0.22);ctx.lineWidth=1;ctx.strokeRect(px-w/2,py-h/2,w,h);
}
function scaffold(b,px,py,h){
  ctx.strokeStyle=L([126,92,52],0.95);ctx.lineWidth=1.7;
  const w=b.w*HW*0.9;
  for(const sx of [-1,1]){
    ctx.beginPath();ctx.moveTo(px+sx*w*0.5,py+4);ctx.lineTo(px+sx*w*0.42,py-h);ctx.stroke();
  }
  ctx.beginPath();ctx.moveTo(px-w*0.46,py-h*0.55);ctx.lineTo(px+w*0.46,py-h*0.55);ctx.stroke();
  ctx.beginPath();ctx.moveTo(px-w*0.42,py-h*0.95);ctx.lineTo(px+w*0.42,py-h*0.95);ctx.stroke();
}

/* ── buildings ────────────────────────────────────────────────────────── */
const PLASTER=[232,218,192],TIMBER=[88,58,36],THATCH=[176,132,68],TILE=[154,70,56],STONE=[146,146,152],WOOD=[142,102,60],DARKW=[92,64,40];
function drawBuilding(b,time){
  const d=BDEF[b.def];
  const x0=b.x,y0=b.y,x1=b.x+b.w,y1=b.y+b.h;
  const px=isoX((x0+x1)*0.5,(y0+y1)*0.5), py=isoY((x0+x1)*0.5,(y0+y1)*0.5);
  const A=ambience();
  const lit=isNight();
  const under=b.built<1;
  shadow(px,py,(b.w*HW*0.55+6),(b.h*HH*0.55+4),0.28*AMB);

  if(under){
    // foundation + partial build
    const p=clamp(b.built,0,1);
    ctx.fillStyle=L([96,86,72],0.9);
    ctx.beginPath();
    ctx.moveTo(isoX(x0,y0),isoY(x0,y0));ctx.lineTo(isoX(x1,y0),isoY(x1,y0));
    ctx.lineTo(isoX(x1,y1),isoY(x1,y1));ctx.lineTo(isoX(x0,y1),isoY(x0,y1));ctx.closePath();ctx.fill();
    ctx.strokeStyle=css([255,214,140],0.30+Math.sin(time*3)*0.12);ctx.lineWidth=1.4;ctx.stroke();
    if(p>0.05){
      const H=(b.def==="tower"?44:b.def==="wall"?16:20)*p;
      isoBox(x0+0.08,y0+0.08,x1-0.08,y1-0.08,H,L(TIMBER,0.8),L(TIMBER,0.62),L(TIMBER,0.5));
      scaffold(b,px,py,max(24,H+14));
      // material pile
      for(const k in b.mats){
        if(k==="wood"){ctx.fillStyle=L([142,102,60]);for(let i=0;i<3;i++){ctx.fillRect(px-14+i*7,py-4+i*1.6,10,3);}}
        else if(k==="stone"){ctx.fillStyle=L([150,150,158]);for(let i=0;i<3;i++){ctx.beginPath();ctx.arc(px+8+i*4,py+4-i*1.4,3,0,TAU);ctx.fill();}}
      }
    }
    drawProgress(b,px,py-max(30,20*p)-16);
    return;
  }

  switch(b.def){
    case "road": break;
    case "house": {
      const wh=17+b.quality*1.5;
      isoBox(x0,y0,x1,y1,5,L(STONE,0.82),L(STONE,0.62),L(STONE,0.5));
      isoBox(x0+0.04,y0+0.04,x1-0.04,y1-0.04,wh,L(PLASTER,1.02),L(PLASTER,0.8),L(PLASTER,0.62));
      // timber framing
      ctx.strokeStyle=L(TIMBER,0.92);ctx.lineWidth=1.9;
      const dx=isoX(x0,y1),dy=isoY(x0,y1),cx=isoX(x1,y1),cy=isoY(x1,y1),bx=isoX(x1,y0),by=isoY(x1,y0);
      ctx.beginPath();
      ctx.moveTo(dx,dy-5);ctx.lineTo(cx,cy-5);ctx.lineTo(bx,by-5);
      ctx.moveTo(dx,dy-wh);ctx.lineTo(cx,cy-wh);ctx.lineTo(bx,by-wh);
      ctx.moveTo((dx+cx)/2,(dy+cy)/2-5);ctx.lineTo((dx+cx)/2,(dy+cy)/2-wh);
      ctx.moveTo((cx+bx)/2,(cy+by)/2-5);ctx.lineTo((cx+bx)/2,(cy+by)/2-wh);
      ctx.stroke();
      gableRoof(x0,y0,x1,y1,wh,13,L(TILE,1.0),L(TILE,0.7));
      // door
      ctx.fillStyle=L(DARKW,0.9);
      const dmx=(dx+cx)/2,dmy=(dy+cy)/2;
      ctx.beginPath();ctx.moveTo(dmx-4,dmy-5);ctx.lineTo(dmx+4,dmy-5);ctx.lineTo(dmx+4,dmy-14);ctx.lineTo(dmx-4,dmy-14);ctx.closePath();ctx.fill();
      // windows (glow at night)
      const wx=(cx+bx)/2,wy=(cy+by)/2;
      for(let k=0;k<2;k++){
        const ox=(k?4:-4);
        ctx.fillStyle=lit?css([255,214,140],0.95):L([70,88,110],0.9);
        ctx.fillRect(wx+ox-2.6,wy-13,5.2,5.2);
        ctx.strokeStyle=L(TIMBER);ctx.lineWidth=1;ctx.strokeRect(wx+ox-2.6,wy-13,5.2,5.2);
      }
      // chimney
      const chx=isoX(x0+0.28,y0+0.3),chy=isoY(x0+0.28,y0+0.3);
      ctx.fillStyle=L(STONE,0.86);ctx.fillRect(chx-2.6,chy-wh-19,5.4,12);
      ctx.fillStyle=L(STONE,1.0);ctx.fillRect(chx-3.4,chy-wh-21,7,2.6);
      if(b.quality>0){ctx.fillStyle=L([196,150,80]);for(let k=0;k<b.quality;k++){ctx.fillRect(dx+6+k*5,dy-wh+2,3.4,3.4);}}
      break;
    }
    case "stock": {
      isoBox(x0,y0,x1,y1,4,L(STONE,0.8),L(STONE,0.6),L(STONE,0.48));
      // posts
      ctx.strokeStyle=L(TIMBER);ctx.lineWidth=2.6;
      for(const c of [[x0+0.14,y0+0.14],[x1-0.14,y0+0.14],[x1-0.14,y1-0.14],[x0+0.14,y1-0.14]]){
        ctx.beginPath();ctx.moveTo(isoX(c[0],c[1]),isoY(c[0],c[1])-4);ctx.lineTo(isoX(c[0],c[1]),isoY(c[0],c[1])-18);ctx.stroke();
      }
      // crates
      for(let k=0;k<5;k++){
        const gx=x0+0.35+(k%3)*((b.w-0.7)/2.4), gy=y0+0.4+((k/3)|0)*((b.h-0.8)/1.8);
        const cx2=isoX(gx,gy),cy2=isoY(gx,gy);
        isoBox(gx,gy,gx+0.42,gy+0.42,7,L([178,138,84]),L([146,110,64]),L([112,82,48]));
      }
      // canvas roof
      const cx0=x0-0.12,cy0=y0-0.12,cx1=x1+0.12,cy1=y1+0.12;
      ctx.fillStyle=L([214,198,164],1.0);
      ctx.beginPath();
      ctx.moveTo(isoX(cx0,(cy0+cy1)/2),isoY(cx0,(cy0+cy1)/2)-26);
      ctx.lineTo(isoX(cx1,(cy0+cy1)/2),isoY(cx1,(cy0+cy1)/2)-26);
      ctx.lineTo(isoX(cx1,cy1),isoY(cx1,cy1)-17);
      ctx.lineTo(isoX(cx0,cy1),isoY(cx0,cy1)-17);
      ctx.closePath();ctx.fill();
      ctx.fillStyle=L([190,174,142],0.9);
      ctx.beginPath();
      ctx.moveTo(isoX(cx0,(cy0+cy1)/2),isoY(cx0,(cy0+cy1)/2)-26);
      ctx.lineTo(isoX(cx1,(cy0+cy1)/2),isoY(cx1,(cy0+cy1)/2)-26);
      ctx.lineTo(isoX(cx1,cy0),isoY(cx1,cy0)-17);
      ctx.lineTo(isoX(cx0,cy0),isoY(cx0,cy0)-17);
      ctx.closePath();ctx.fill();
      break;
    }
    case "workshop": {
      const wh=19;
      isoBox(x0,y0,x1,y1,5,L(STONE,0.8),L(STONE,0.6),L(STONE,0.48));
      isoBox(x0+0.04,y0+0.04,x1-0.04,y1-0.04,wh,L([122,90,58],1.0),L([104,74,46],0.9),L([82,58,36],0.9));
      gableRoof(x0,y0,x1,y1,wh,11,L([96,72,52],1.0),L([74,54,38],0.8));
      // big doors
      const dx=isoX(x0,y1),dy=isoY(x0,y1),cx=isoX(x1,y1),cy=isoY(x1,y1);
      ctx.fillStyle=L([64,46,30]);
      ctx.beginPath();ctx.moveTo((dx+cx)/2-9,(dy+cy)/2-5);ctx.lineTo((dx+cx)/2+9,(dy+cy)/2-5);
      ctx.lineTo((dx+cx)/2+9,(dy+cy)/2-16);ctx.lineTo((dx+cx)/2-9,(dy+cy)/2-16);ctx.closePath();ctx.fill();
      // anvil + tools
      ctx.fillStyle=L([70,72,80]);ctx.fillRect(px+8,py-9,7,4);
      ctx.strokeStyle=L([150,120,80]);ctx.lineWidth=1.4;
      ctx.beginPath();ctx.moveTo(px-12,py-6);ctx.lineTo(px-8,py-15);ctx.stroke();
      const chx=isoX(x1-0.3,y0+0.3),chy=isoY(x1-0.3,y0+0.3);
      ctx.fillStyle=L(STONE,0.86);ctx.fillRect(chx-3,chy-wh-16,6,11);
      break;
    }
    case "market": {
      isoBox(x0,y0,x1,y1,6,L(STONE,0.82),L(STONE,0.62),L(STONE,0.5));
      // stalls with striped awnings
      for(let k=0;k<2;k++){
        const sx=x0+0.18+k*(b.w-0.5)/1.6, sy=y0+0.3;
        isoBox(sx,sy,sx+0.7,sy+0.9,9,L([150,112,66]),L([124,90,52]),L([100,72,42]));
        const ax0=sx-0.08,ax1=sx+0.78,ay0=sy-0.06,ay1=sy+0.98;
        for(let st=0;st<5;st++){
          ctx.fillStyle=L(st%2?[214,86,70]:[238,232,216],1.0);
          const t0=st/5,t1=(st+1)/5;
          ctx.beginPath();
          ctx.moveTo(isoX(lerp(ax0,ax1,t0),ay1),isoY(lerp(ax0,ax1,t0),ay1)-19);
          ctx.lineTo(isoX(lerp(ax0,ax1,t1),ay1),isoY(lerp(ax0,ax1,t1),ay1)-19);
          ctx.lineTo(isoX(lerp(ax0,ax1,t1),ay0),isoY(lerp(ax0,ax1,t1),ay0)-23);
          ctx.lineTo(isoX(lerp(ax0,ax1,t0),ay0),isoY(lerp(ax0,ax1,t0),ay0)-23);
          ctx.closePath();ctx.fill();
        }
        // goods
        ctx.fillStyle=L([232,196,90]);ctx.beginPath();ctx.arc(isoX(sx+0.25,sy+0.45),isoY(sx+0.25,sy+0.45)-11,2.4,0,TAU);ctx.fill();
        ctx.fillStyle=L([120,180,96]);ctx.beginPath();ctx.arc(isoX(sx+0.45,sy+0.5),isoY(sx+0.45,sy+0.5)-11,2.4,0,TAU);ctx.fill();
      }
      if(G.market.here){
        ctx.fillStyle=css([246,206,120],0.6+Math.sin(time*3)*0.25);
        ctx.beginPath();ctx.arc(px,py-30,2.6,0,TAU);ctx.fill();
      }
      break;
    }
    case "infirm": {
      const wh=16;
      isoBox(x0,y0,x1,y1,4,L(STONE,0.82),L(STONE,0.62),L(STONE,0.5));
      isoBox(x0+0.04,y0+0.04,x1-0.04,y1-0.04,wh,L([240,240,238],1.0),L([224,226,228],0.92),L([198,202,208],0.92));
      gableRoof(x0,y0,x1,y1,wh,10,L([92,124,150],1.0),L([70,98,122],0.8));
      // red cross banner
      const dx=isoX(x0,y1),dy=isoY(x0,y1),cx=isoX(x1,y1),cy=isoY(x1,y1);
      const mx=(dx+cx)/2,my=(dy+cy)/2;
      ctx.fillStyle=L([226,226,222]);ctx.fillRect(mx-7,my-wh+1,14,12);
      ctx.fillStyle=L([206,64,58]);ctx.fillRect(mx-1.8,my-wh+3.4,3.6,7.4);ctx.fillRect(mx-4.6,my-wh+6.2,9.2,2.6);
      break;
    }
    case "mine": {
      isoBox(x0,y0,x1,y1,3,L([86,80,74]),L([68,62,58]),L([54,50,46]));
      // dark entrance
      const ex=(x0+x1)/2,ey=(y0+y1)/2;
      ctx.fillStyle=css([12,10,10],0.95);
      ctx.beginPath();ctx.ellipse(isoX(ex,ey+0.28),isoY(ex,ey+0.28)-6,11,9,0,PI,TAU);ctx.fill();
      ctx.fillRect(isoX(ex,ey+0.28)-11,isoY(ex,ey+0.28)-6,22,7);
      // headframe
      ctx.strokeStyle=L(TIMBER,0.95);ctx.lineWidth=2.4;
      const hx=isoX(ex,ey-0.2),hy=isoY(ex,ey-0.2);
      ctx.beginPath();ctx.moveTo(hx-13,hy+2);ctx.lineTo(hx,hy-30);ctx.lineTo(hx+13,hy+2);ctx.stroke();
      ctx.beginPath();ctx.moveTo(hx-8,hy-12);ctx.lineTo(hx+8,hy-12);ctx.stroke();
      ctx.strokeStyle=L([190,180,160],0.8);ctx.lineWidth=1;
      ctx.beginPath();ctx.moveTo(hx,hy-30);ctx.lineTo(hx,hy-16);ctx.stroke();
      ctx.fillStyle=L([120,110,96]);ctx.fillRect(hx-3.4,hy-17,6.8,5);
      // ore cart
      ctx.fillStyle=L([110,84,54]);ctx.fillRect(px+10,py-6,12,6);
      ctx.fillStyle=L([150,150,158]);
      for(let k=0;k<3;k++){ctx.beginPath();ctx.arc(px+13+k*4,py-7,2,0,TAU);ctx.fill();}
      break;
    }
    case "wall": {
      const hh=17;
      isoBox(x0+0.06,y0+0.06,x1-0.06,y1-0.06,hh,L(STONE,1.0),L(STONE,0.74),L(STONE,0.58));
      // crenellations
      ctx.fillStyle=L(STONE,0.94);
      for(let k=0;k<3;k++){
        const t=(k+0.5)/3;
        const cx2=isoX(lerp(x0,x1,t),y1),cy2=isoY(lerp(x0,x1,t),y1);
        ctx.fillRect(cx2-2.4,cy2-hh-4,4.8,4);
      }
      // stone joints
      ctx.strokeStyle=css([0,0,0],0.16);ctx.lineWidth=0.8;
      for(let k=1;k<3;k++){
        const yy=isoY(x0,y1)-hh*k/3;
        ctx.beginPath();ctx.moveTo(isoX(x0,y1),yy);ctx.lineTo(isoX(x1,y1),isoY(x1,y1)-hh*k/3);ctx.stroke();
      }
      if(SNOW>0.2){ctx.fillStyle=css([240,247,255],SNOW*0.6*AMB);
        ctx.beginPath();ctx.moveTo(isoX(x0,y0),isoY(x0,y0)-hh-1);ctx.lineTo(isoX(x1,y0),isoY(x1,y0)-hh-1);
        ctx.lineTo(isoX(x1,y1),isoY(x1,y1)-hh-1);ctx.lineTo(isoX(x0,y1),isoY(x0,y1)-hh-1);ctx.closePath();ctx.fill();}
      break;
    }
    case "tower": {
      const hh=40;
      isoBox(x0+0.1,y0+0.1,x1-0.1,y1-0.1,hh,L(STONE,1.0),L(STONE,0.72),L(STONE,0.56));
      isoBox(x0-0.06,y0-0.06,x1+0.06,y1+0.06,4,L(TIMBER,1.0),L(TIMBER,0.78),L(TIMBER,0.6));
      // platform on top
      const ty=isoY(x0,y0)-hh-4;
      ctx.fillStyle=L(TIMBER,0.9);
      ctx.beginPath();
      ctx.moveTo(isoX(x0-0.1,y0-0.1),isoY(x0-0.1,y0-0.1)-hh-4);
      ctx.lineTo(isoX(x1+0.1,y0-0.1),isoY(x1+0.1,y0-0.1)-hh-4);
      ctx.lineTo(isoX(x1+0.1,y1+0.1),isoY(x1+0.1,y1+0.1)-hh-4);
      ctx.lineTo(isoX(x0-0.1,y1+0.1),isoY(x0-0.1,y1+0.1)-hh-4);
      ctx.closePath();ctx.fill();
      // conical roof
      const cxx=isoX((x0+x1)/2,(y0+y1)/2), cyy=isoY((x0+x1)/2,(y0+y1)/2);
      ctx.fillStyle=L(TILE,1.0);
      ctx.beginPath();ctx.moveTo(cxx,cyy-hh-26);ctx.lineTo(cxx-16,cyy-hh-2);ctx.lineTo(cxx+16,cyy-hh-2);ctx.closePath();ctx.fill();
      ctx.fillStyle=L(TILE,0.72);
      ctx.beginPath();ctx.moveTo(cxx,cyy-hh-26);ctx.lineTo(cxx+16,cyy-hh-2);ctx.lineTo(cxx+5,cyy-hh+3);ctx.closePath();ctx.fill();
      // flag
      ctx.strokeStyle=L([120,100,80]);ctx.lineWidth=1.3;
      ctx.beginPath();ctx.moveTo(cxx,cyy-hh-26);ctx.lineTo(cxx,cyy-hh-38);ctx.stroke();
      const fl=Math.sin(time*3.4)*2.4;
      ctx.fillStyle=L([226,180,90]);
      ctx.beginPath();ctx.moveTo(cxx,cyy-hh-38);ctx.lineTo(cxx+11+fl,cyy-hh-35);ctx.lineTo(cxx,cyy-hh-31);ctx.closePath();ctx.fill();
      // arrow slits
      ctx.fillStyle=css([20,18,18],0.8);
      ctx.fillRect(isoX(x1-0.1,y0+0.4)-1.4,isoY(x1-0.1,y0+0.4)-hh*0.6,2.8,7);
      break;
    }
    case "well": {
      isoBox(x0+0.18,y0+0.18,x1-0.18,y1-0.18,9,L(STONE,0.9),L(STONE,0.68),L(STONE,0.54));
      ctx.fillStyle=css([26,44,62],0.95);
      ctx.beginPath();ctx.ellipse(px,py-9,8,4,0,0,TAU);ctx.fill();
      ctx.fillStyle=css([70,130,170],0.5+Math.sin(time*2)*0.12);
      ctx.beginPath();ctx.ellipse(px,py-8.4,6.4,3,0,0,TAU);ctx.fill();
      ctx.strokeStyle=L(TIMBER);ctx.lineWidth=2;
      ctx.beginPath();ctx.moveTo(px-8,py-9);ctx.lineTo(px-8,py-24);ctx.moveTo(px+8,py-9);ctx.lineTo(px+8,py-24);ctx.stroke();
      ctx.fillStyle=L([120,86,52]);
      ctx.beginPath();ctx.moveTo(px-11,py-24);ctx.lineTo(px+11,py-24);ctx.lineTo(px,py-32);ctx.closePath();ctx.fill();
      break;
    }
    case "bonfire": {
      // stone ring
      for(let k=0;k<7;k++){
        const a=k/7*TAU;
        ctx.fillStyle=L(shade(STONE,0.8+((k*37)%10)/40));
        ctx.beginPath();ctx.ellipse(px+Math.cos(a)*10,py+Math.sin(a)*5,3.4,2.4,0,0,TAU);ctx.fill();
      }
      ctx.fillStyle=L([52,40,30]);
      ctx.beginPath();ctx.ellipse(px,py,7,3.4,0,0,TAU);ctx.fill();
      ctx.strokeStyle=L([104,74,44]);ctx.lineWidth=2.2;
      for(let k=0;k<3;k++){const a=k*2.1;
        ctx.beginPath();ctx.moveTo(px-6*Math.cos(a),py-3*Math.sin(a));ctx.lineTo(px+6*Math.cos(a),py-8+3*Math.sin(a));ctx.stroke();}
      // flame
      const fl=0.75+Math.sin(time*11)*0.14+Math.sin(time*17.3)*0.1;
      const fh=15*fl;
      const gr=ctx.createRadialGradient(px,py-fh*0.4,1,px,py-fh*0.4,fh*1.5);
      gr.addColorStop(0,"rgba(255,246,206,.95)");gr.addColorStop(.35,"rgba(255,176,60,.72)");gr.addColorStop(1,"rgba(255,90,20,0)");
      ctx.fillStyle=gr;ctx.beginPath();ctx.arc(px,py-fh*0.4,fh*1.5,0,TAU);ctx.fill();
      ctx.fillStyle="rgba(255,168,52,.92)";
      ctx.beginPath();ctx.moveTo(px-6,py-2);
      ctx.quadraticCurveTo(px-3+Math.sin(time*9)*2,py-fh*0.6,px,py-fh);
      ctx.quadraticCurveTo(px+3+Math.sin(time*8+1)*2,py-fh*0.6,px+6,py-2);ctx.closePath();ctx.fill();
      ctx.fillStyle="rgba(255,240,190,.95)";
      ctx.beginPath();ctx.moveTo(px-3,py-2);
      ctx.quadraticCurveTo(px-1.4,py-fh*0.5,px,py-fh*0.74);
      ctx.quadraticCurveTo(px+1.4,py-fh*0.5,px+3,py-2);ctx.closePath();ctx.fill();
      if(!NOFX&&chance(0.16))spawnParticle(b.x+0.5,b.y+0.5,"fire");
      if(!NOFX&&chance(0.05))spawnParticle(b.x+0.5,b.y+0.5,"smoke");
      break;
    }
    case "lamp": {
      ctx.strokeStyle=L([62,54,48]);ctx.lineWidth=2.4;
      ctx.beginPath();ctx.moveTo(px,py);ctx.lineTo(px,py-26);ctx.stroke();
      ctx.fillStyle=L([52,46,42]);ctx.beginPath();ctx.ellipse(px,py,5,2.4,0,0,TAU);ctx.fill();
      const gl=0.72+Math.sin(time*7.1+b.seed)*0.1;
      const gr=ctx.createRadialGradient(px,py-29,1,px,py-29,17*gl);
      gr.addColorStop(0,"rgba(255,232,168,.98)");gr.addColorStop(.4,"rgba(255,190,96,.42)");gr.addColorStop(1,"rgba(255,160,60,0)");
      ctx.fillStyle=gr;ctx.beginPath();ctx.arc(px,py-29,17*gl,0,TAU);ctx.fill();
      ctx.fillStyle=L([58,50,44]);
      ctx.beginPath();ctx.moveTo(px-4.4,py-26);ctx.lineTo(px+4.4,py-26);ctx.lineTo(px+2.6,py-33);ctx.lineTo(px-2.6,py-33);ctx.closePath();ctx.fill();
      break;
    }
    case "statue": {
      isoBox(x0+0.1,y0+0.1,x1-0.1,y1-0.1,12,L(STONE,1.0),L(STONE,0.78),L(STONE,0.62));
      const cx2=isoX((x0+x1)/2,(y0+y1)/2),cy2=isoY((x0+x1)/2,(y0+y1)/2);
      ctx.fillStyle=L([186,186,192],1.0);
      ctx.fillRect(cx2-4.4,cy2-34,8.8,22);
      ctx.beginPath();ctx.arc(cx2,cy2-38,4.8,0,TAU);ctx.fill();
      ctx.strokeStyle=L([186,186,192]);ctx.lineWidth=3;ctx.lineCap="round";
      ctx.beginPath();ctx.moveTo(cx2-2,cy2-31);ctx.lineTo(cx2-8,cy2-40);ctx.stroke();
      ctx.beginPath();ctx.moveTo(cx2+2,cy2-31);ctx.lineTo(cx2+7,cy2-25);ctx.stroke();
      ctx.fillStyle=css([255,220,150],0.16+Math.sin(time*1.6)*0.06);
      ctx.beginPath();ctx.arc(cx2,cy2-34,20,0,TAU);ctx.fill();
      break;
    }
    case "farm": break;
    case "orchard": {
      const m=b.maturity===undefined?0.05:b.maturity;
      ctx.fillStyle=L(shade([96,66,44],0.94));
      ctx.beginPath();
      ctx.moveTo(isoX(x0,y0),isoY(x0,y0));ctx.lineTo(isoX(x1,y0),isoY(x1,y0));
      ctx.lineTo(isoX(x1,y1),isoY(x1,y1));ctx.lineTo(isoX(x0,y1),isoY(x0,y1));ctx.closePath();ctx.fill();
      for(let k=0;k<4;k++){
        const gx=x0+0.5+(k%2)*(b.w-1), gy=y0+0.5+((k/2)|0)*(b.h-1);
        drawOrchardTree(isoX(gx,gy),isoY(gx,gy),m,time);
      }
      // fence
      ctx.strokeStyle=L(TIMBER,0.9);ctx.lineWidth=1.4;
      ctx.beginPath();
      ctx.moveTo(isoX(x0,y0),isoY(x0,y0)-7);ctx.lineTo(isoX(x1,y0),isoY(x1,y0)-7);
      ctx.lineTo(isoX(x1,y1),isoY(x1,y1)-7);ctx.stroke();
      break;
    }
  }
  // damage cracks
  if(b.hp<b.maxhp*0.55){
    ctx.strokeStyle=css([20,16,14],0.45);ctx.lineWidth=1.2;
    ctx.beginPath();ctx.moveTo(px-8,py-8);ctx.lineTo(px-3,py-14);ctx.lineTo(px+2,py-9);ctx.stroke();
  }
  // fire on building
  if(b.fire>0){}
}
function drawOrchardTree(px,py,m,time){
  const s=0.55+m*0.5;
  shadow(px,py,9*s,3.6*s,0.26*AMB);
  ctx.strokeStyle=L([92,64,40]);ctx.lineWidth=2.4*s;
  ctx.beginPath();ctx.moveTo(px,py);ctx.lineTo(px,py-14*s);ctx.stroke();
  const g=G.season===3?[150,156,150]:(G.season===2?[158,152,72]:VEG[0]);
  for(let k=0;k<3;k++){
    ctx.fillStyle=L(shade(g,0.8+k*0.12));
    ctx.beginPath();ctx.arc(px+(k-1)*4.4*s,py-16*s-(k===1?2*s:0),5.4*s,0,TAU);ctx.fill();
  }
  if(G.season>=1&&G.season<=2&&m>0.3){
    ctx.fillStyle=L([214,72,62]);
    for(let k=0;k<4;k++){const a=k*1.7+m*5;ctx.beginPath();ctx.arc(px+Math.cos(a)*5*s,py-16*s+Math.sin(a)*3.4*s,1.7*s,0,TAU);ctx.fill();}
  }
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 10 · units, items, lighting, weather, main render
═══════════════════════════════════════════════════════════════════════════════*/

function drawHumanoid(px,py,o,time){
  // o: {skin,hair,shirt,walk,moving,act,flip,scale,hairStyle,carry,tool}
  const s=o.scale||1;
  const wk=o.walk||0;
  const swing=o.moving?Math.sin(wk)*3.4*s:0;
  const bob=o.moving?Math.abs(Math.sin(wk))*1.3*s:Math.sin(time*1.7+px*0.1)*0.5*s;
  const f=o.flip?-1:1;
  shadow(px,py,4.6*s,2.1*s,0.30*AMB);
  const hy=py-13.4*s-bob;
  // legs
  ctx.strokeStyle=L(shade(o.shirt,0.5),1);ctx.lineWidth=2.2*s;ctx.lineCap="round";
  ctx.beginPath();ctx.moveTo(px-1.5*s*f,hy+7.4*s);ctx.lineTo(px-1.5*s*f+swing*0.55,py);ctx.stroke();
  ctx.beginPath();ctx.moveTo(px+1.5*s*f,hy+7.4*s);ctx.lineTo(px+1.5*s*f-swing*0.55,py);ctx.stroke();
  // torso
  ctx.fillStyle=L(o.shirt);
  ctx.beginPath();
  ctx.moveTo(px-3.3*s,hy+2.2*s);ctx.lineTo(px+3.3*s,hy+2.2*s);
  ctx.lineTo(px+2.7*s,hy+8.2*s);ctx.lineTo(px-2.7*s,hy+8.2*s);ctx.closePath();ctx.fill();
  ctx.fillStyle=css([255,255,255],0.07*AMB);
  ctx.fillRect(px-3.3*s,hy+2.2*s,1.6*s,6*s);
  // arms
  const armA=o.act==="work"?Math.sin(time*11)*0.9-0.6:swing*0.16;
  ctx.strokeStyle=L(shade(o.shirt,0.82));ctx.lineWidth=1.9*s;
  ctx.beginPath();ctx.moveTo(px-3*s,hy+3*s);
  ctx.lineTo(px-3*s-Math.cos(armA)*3.4*s*f,hy+3*s+Math.sin(armA+1.4)*3.6*s);ctx.stroke();
  ctx.beginPath();ctx.moveTo(px+3*s,hy+3*s);
  ctx.lineTo(px+3*s+Math.cos(armA)*3.4*s*f,hy+3*s+Math.sin(armA+1.4)*3.6*s);ctx.stroke();
  // tool in hand while working
  if(o.act==="work"&&o.tool){
    const tx=px+3.6*s*f+Math.cos(armA)*3.4*s*f, ty=hy+3*s+Math.sin(armA+1.4)*3.6*s;
    ctx.strokeStyle=L([126,90,52]);ctx.lineWidth=1.5*s;
    ctx.beginPath();ctx.moveTo(tx,ty);ctx.lineTo(tx+5*s*f,ty-6*s);ctx.stroke();
    ctx.fillStyle=L([178,182,190]);ctx.fillRect(tx+3.4*s*f,ty-8.4*s,4*s,3*s);
  }
  // head
  ctx.fillStyle=L(o.skin);
  ctx.beginPath();ctx.arc(px+f*0.5*s,hy,3.3*s,0,TAU);ctx.fill();
  // hair
  ctx.fillStyle=L(o.hair);
  if(o.hairStyle===0){ctx.beginPath();ctx.arc(px+f*0.5*s,hy-0.7*s,3.4*s,PI*1.05,PI*2.05);ctx.fill();}
  else if(o.hairStyle===1){ctx.beginPath();ctx.arc(px+f*0.5*s,hy-0.4*s,3.5*s,PI*0.95,PI*2.15);ctx.fill();
    ctx.fillRect(px-f*3.4*s,hy-1.2*s,1.7*s,4.6*s);}
  else if(o.hairStyle===2){ctx.beginPath();ctx.arc(px+f*0.5*s,hy-0.6*s,3.5*s,PI*1.1,PI*2.0);ctx.fill();
    ctx.beginPath();ctx.arc(px-f*2.4*s,hy+1.2*s,2*s,0,TAU);ctx.fill();}
  else {ctx.beginPath();ctx.arc(px+f*0.5*s,hy-0.8*s,3.3*s,PI*1.15,PI*1.95);ctx.fill();}
  // carried bundle
  if(o.carry){
    const cc=({wood:[150,106,58],stone:[154,154,162],food:[214,182,92],cloth:[196,164,214],tools:[184,190,200]})[o.carry]||[180,180,180];
    ctx.fillStyle=L(cc);
    ctx.beginPath();ctx.ellipse(px-4.2*s*f,hy+5.4*s,3.2*s,2.5*s,0,0,TAU);ctx.fill();
    ctx.strokeStyle=css([0,0,0],0.2);ctx.lineWidth=0.7;ctx.stroke();
  }
  return hy;
}

function drawColonist(c,time){
  const px=isoX(c.x,c.y), py=isoY(c.x,c.y);
  const sleeping=c.state==="sleeping"&&c.energy<96&&!c.moving;
  const vx=c.moving?Math.cos(c.dir):0;
  if(sleeping){
    shadow(px,py,6,2.6,0.26*AMB);
    ctx.fillStyle=L(shade(c.cloth,0.82));
    ctx.beginPath();ctx.ellipse(px,py-3,7,3.4,0,0,TAU);ctx.fill();
    ctx.fillStyle=L(c.skin);
    ctx.beginPath();ctx.arc(px-6,py-4.2,2.9,0,TAU);ctx.fill();
    const z=(time*1.1)%2;
    ctx.fillStyle=css([220,232,255],0.5-z*0.2);
    ctx.font="bold 8px ui-monospace,monospace";ctx.fillText("z",px+5+z*3,py-8-z*5);
    return;
  }
  const act=(c.state==="working"||c.state==="fighting")?"work":"idle";
  const hy=drawHumanoid(px,py,{skin:c.skin,hair:c.hair,shirt:c.cloth,walk:c.walk,moving:c.moving,
    act,flip:vx<0,scale:c.age<16?0.74:0.92,hairStyle:c.hairStyle,carry:c.carry?c.carry.kind:null,tool:c.tool},time);
  // militia marker
  if(c.militia){
    ctx.strokeStyle=L([186,190,200]);ctx.lineWidth=1.3;
    ctx.beginPath();ctx.moveTo(px+4.6,py-16);ctx.lineTo(px+4.6,py-25);ctx.stroke();
    ctx.fillStyle=L([120,124,132]);ctx.beginPath();ctx.moveTo(px+4.6,py-25);ctx.lineTo(px+8.4,py-23.4);ctx.lineTo(px+4.6,py-21.6);ctx.closePath();ctx.fill();
  }
  // needs alerts
  let icons=[];
  if(c.hunger<26)icons.push(["#f0d060","h"]);
  if(c.energy<20)icons.push(["#8fb6e8","e"]);
  if(c.health<55)icons.push(["#f0685a","+"]);
  if(c.breakT>0)icons.push(["#f0685a","!"]);
  for(let k=0;k<icons.length;k++){
    const yy=py-27-k*8, xx=px+8;
    ctx.fillStyle=icons[k][0];
    ctx.beginPath();ctx.arc(xx,yy,3.1,0,TAU);ctx.fill();
    ctx.fillStyle="rgba(10,12,18,.9)";ctx.font="bold 5px ui-monospace,monospace";ctx.textAlign="center";
    ctx.fillText(icons[k][1],xx,yy+1.8);ctx.textAlign="left";
  }
  // mood face when selected
  if(G.sel&&G.sel.type==="col"&&G.sel.id===c.id){
    ctx.strokeStyle=css([242,180,92],0.85);ctx.lineWidth=1.5;
    ctx.beginPath();ctx.ellipse(px,py,9,4.4,0,0,TAU);ctx.stroke();
    ctx.strokeStyle=css([242,180,92],0.25);
    ctx.beginPath();ctx.ellipse(px,py,12,6,0,0,TAU);ctx.stroke();
  }
  // thought bubble
  if(c.thoughtT>0&&G.cam.z>0.72){
    ctx.font="9px "+getComputedStyle(document.body).fontFamily;
    const w=ctx.measureText(c.thought).width+8;
    ctx.fillStyle=css([12,16,24],0.78);
    roundRect(px-w/2,py-42,w,13,5);ctx.fill();
    ctx.fillStyle=css([232,238,248],0.95);ctx.textAlign="center";
    ctx.fillText(c.thought,px,py-32.6);ctx.textAlign="left";
  }
}
function roundRect(x,y,w,h,r){
  ctx.beginPath();
  ctx.moveTo(x+r,y);ctx.lineTo(x+w-r,y);ctx.quadraticCurveTo(x+w,y,x+w,y+r);
  ctx.lineTo(x+w,y+h-r);ctx.quadraticCurveTo(x+w,y+h,x+w-r,y+h);
  ctx.lineTo(x+r,y+h);ctx.quadraticCurveTo(x,y+h,x,y+h-r);
  ctx.lineTo(x,y+r);ctx.quadraticCurveTo(x,y,x+r,y);ctx.closePath();
}

function drawWolf(e,time){
  const px=isoX(e.x,e.y),py=isoY(e.x,e.y);
  const f=e.dir>PI/2||e.dir<-PI/2?-1:1;
  const wk=e.walk,sw=Math.sin(wk)*2.6;
  shadow(px,py,6.4,2.6,0.3*AMB);
  const body=[124,128,136],dark=[86,90,98];
  ctx.strokeStyle=L(dark);ctx.lineWidth=1.7;ctx.lineCap="round";
  for(const o of [-3.4,-1.2,1.4,3.6]){ctx.beginPath();ctx.moveTo(px+o,py-4.4);ctx.lineTo(px+o+sw*(o>0?1:-1)*0.5,py);ctx.stroke();}
  ctx.fillStyle=L(body);
  ctx.beginPath();ctx.ellipse(px,py-6.2,7.4,3.6,0,0,TAU);ctx.fill();
  ctx.fillStyle=L(shade(body,0.78));
  ctx.beginPath();ctx.ellipse(px,py-4.8,6.4,2.2,0,0,TAU);ctx.fill();
  // head
  const hx=px+7.6*f,hy2=py-8.4;
  ctx.fillStyle=L(body);ctx.beginPath();ctx.ellipse(hx,hy2,3.6,2.9,0,0,TAU);ctx.fill();
  ctx.fillStyle=L(shade(body,0.9));ctx.beginPath();ctx.moveTo(hx+3.4*f,hy2);ctx.lineTo(hx+6.4*f,hy2+0.8);ctx.lineTo(hx+3.2*f,hy2+1.8);ctx.closePath();ctx.fill();
  // ears
  ctx.fillStyle=L(dark);
  ctx.beginPath();ctx.moveTo(hx-1.6*f,hy2-2.2);ctx.lineTo(hx-0.4*f,hy2-5.2);ctx.lineTo(hx+1*f,hy2-2.2);ctx.closePath();ctx.fill();
  ctx.beginPath();ctx.moveTo(hx+1.2*f,hy2-2.4);ctx.lineTo(hx+2.6*f,hy2-5);ctx.lineTo(hx+3.4*f,hy2-2);ctx.closePath();ctx.fill();
  // tail
  ctx.strokeStyle=L(body);ctx.lineWidth=2.2;
  ctx.beginPath();ctx.moveTo(px-7*f,py-6.6);ctx.quadraticCurveTo(px-11*f,py-9+Math.sin(time*5)*1.6,px-12.4*f,py-6);ctx.stroke();
  // eyes
  ctx.fillStyle=css([255,150,90],0.9);
  ctx.beginPath();ctx.arc(hx+1.6*f,hy2-0.8,0.9,0,TAU);ctx.fill();
  drawHealthBar(px,py-16,e);
}
function drawBandit(e,time){
  const px=isoX(e.x,e.y),py=isoY(e.x,e.y);
  const vx=Math.cos(e.dir);
  const boss=e.kind==="raider";
  const shirt=boss?[122,52,48]:[104,74,64];
  drawHumanoid(px,py,{skin:[206,168,132],hair:[40,32,28],shirt,walk:e.walk,moving:true,
    act:"work",flip:vx<0,scale:boss?1.1:0.98,hairStyle:3,carry:null,tool:true},time);
  // hood
  ctx.fillStyle=L(shade(shirt,0.8));
  ctx.beginPath();ctx.arc(px,py-16.6,4.2,PI*0.9,PI*2.1);ctx.fill();
  drawHealthBar(px,py-25,e);
  if(boss){
    ctx.fillStyle=css([240,104,90],0.7+Math.sin(time*4)*0.2);
    ctx.beginPath();ctx.arc(px,py-30,2.2,0,TAU);ctx.fill();
  }
}
function drawAnimal(a,time){
  const px=isoX(a.x,a.y),py=isoY(a.x,a.y);
  const f=Math.cos(a.dir)<0?-1:1;
  const sw=Math.sin(a.walk)*2;
  if(a.kind==="deer"){
    shadow(px,py,6,2.4,0.26*AMB);
    ctx.strokeStyle=L([124,90,58]);ctx.lineWidth=1.5;
    for(const o of [-3,3]){ctx.beginPath();ctx.moveTo(px+o,py-5);ctx.lineTo(px+o+sw*(o>0?1:-1)*0.5,py);ctx.stroke();}
    ctx.fillStyle=L([166,120,74]);
    ctx.beginPath();ctx.ellipse(px,py-7,7,3.6,0,0,TAU);ctx.fill();
    ctx.fillStyle=L([198,158,110]);
    ctx.beginPath();ctx.ellipse(px,py-5.6,5.6,1.8,0,0,TAU);ctx.fill();
    const hx=px+6*f,hy=py-11;
    ctx.strokeStyle=L([166,120,74]);ctx.lineWidth=2;
    ctx.beginPath();ctx.moveTo(px+3*f,py-8.4);ctx.lineTo(hx,hy);ctx.stroke();
    ctx.fillStyle=L([178,132,86]);ctx.beginPath();ctx.ellipse(hx+1*f,hy,3,2.2,f*0.3,0,TAU);ctx.fill();
    ctx.strokeStyle=L([120,94,64]);ctx.lineWidth=1.2;
    for(const s of [-1,1]){
      ctx.beginPath();ctx.moveTo(hx,hy-2);
      ctx.lineTo(hx+s*2.4,hy-7);ctx.lineTo(hx+s*4.4,hy-9);ctx.moveTo(hx+s*2.4,hy-7);ctx.lineTo(hx+s*0.6,hy-9.6);ctx.stroke();
    }
    ctx.fillStyle=L([238,232,222]);ctx.beginPath();ctx.ellipse(px-6.4*f,py-7.4,2,1.8,0,0,TAU);ctx.fill();
  } else {
    shadow(px,py,3.4,1.6,0.22*AMB);
    ctx.fillStyle=L([196,188,176]);
    ctx.beginPath();ctx.ellipse(px,py-2.6,4,2.4,0,0,TAU);ctx.fill();
    ctx.beginPath();ctx.arc(px+2.8*f,py-4.6,2.1,0,TAU);ctx.fill();
    ctx.strokeStyle=L([196,188,176]);ctx.lineWidth=1.4;
    ctx.beginPath();ctx.moveTo(px+2*f,py-6);ctx.lineTo(px+1.4*f,py-10);ctx.moveTo(px+3.6*f,py-6);ctx.lineTo(px+4*f,py-10);ctx.stroke();
    ctx.fillStyle=L([240,238,234]);ctx.beginPath();ctx.arc(px-3.8*f,py-3,1.5,0,TAU);ctx.fill();
  }
  if(a.hp<a.maxhp)drawHealthBar(px,py-16,a);
}
function drawHealthBar(px,py,e){
  const w=16,h=2.4,f=clamp(e.hp/e.maxhp,0,1);
  ctx.fillStyle=css([0,0,0],0.6);ctx.fillRect(px-w/2-0.6,py-0.6,w+1.2,h+1.2);
  ctx.fillStyle=css(mixRGB([240,90,72],[110,220,140],f));
  ctx.fillRect(px-w/2,py,w*f,h);
}
function drawItem(it,time){
  const px=isoX(it.x+0.5,it.y+0.5), py=isoY(it.x+0.5,it.y+0.5);
  const bob=Math.sin(time*2+it.bob)*0.9;
  const n=min(4,1+floor(it.amount/6));
  shadow(px,py,6,2.6,0.22*AMB);
  const cols={wood:[[150,106,58],[116,80,42]],stone:[[158,158,166],[112,112,120]],
    food:[[224,192,96],[178,146,64]],cloth:[[200,168,218],[154,124,172]],tools:[[192,198,208],[138,144,154]]};
  const cc=cols[it.kind]||cols.wood;
  for(let k=0;k<n;k++){
    const ox=(k%2?3:-3)+(k>1?1:-1), oy=-k*2.1+bob;
    if(it.kind==="wood"){
      ctx.fillStyle=L(cc[k%2]);ctx.beginPath();ctx.ellipse(px+ox,py+oy-2,5,2.6,0,0,TAU);ctx.fill();
      ctx.fillStyle=L(shade(cc[0],1.2));ctx.beginPath();ctx.ellipse(px+ox-4.4,py+oy-2,1.5,2.4,0,0,TAU);ctx.fill();
    } else if(it.kind==="stone"){
      ctx.fillStyle=L(cc[k%2]);ctx.beginPath();
      ctx.moveTo(px+ox-3.6,py+oy-1);ctx.lineTo(px+ox-1.4,py+oy-4.4);ctx.lineTo(px+ox+2.6,py+oy-3.6);
      ctx.lineTo(px+ox+3.8,py+oy-0.4);ctx.closePath();ctx.fill();
    } else if(it.kind==="tools"){
      ctx.strokeStyle=L([126,90,52]);ctx.lineWidth=1.6;
      ctx.beginPath();ctx.moveTo(px+ox-3,py+oy);ctx.lineTo(px+ox+2,py+oy-5);ctx.stroke();
      ctx.fillStyle=L(cc[0]);ctx.fillRect(px+ox+1,py+oy-7,4,2.6);
    } else {
      ctx.fillStyle=L(cc[k%2]);ctx.beginPath();
      ctx.moveTo(px+ox-4,py+oy);ctx.quadraticCurveTo(px+ox,py+oy-7,px+ox+4,py+oy);ctx.closePath();ctx.fill();
      ctx.strokeStyle=L(shade(cc[1],0.8));ctx.lineWidth=0.8;ctx.stroke();
    }
  }
  if(it.pop>0){it.pop-=0.03;}
}

/* ── particles (world space) ──────────────────────────────────────────── */
function drawParticles(){
  ctx.lineCap="round";
  for(const p of G.particles){
    const px=isoX(p.x,p.y), py=isoY(p.x,p.y);
    const t=1-p.life/p.max;
    const a=(p.fade===0.5||p.fade===0.6)?(1-t*t)*p.fade*1.4:(1-t);
    if(a<=0)continue;
    const col=p.col;
    if(p.add){
      ctx.globalCompositeOperation="lighter";
      ctx.fillStyle=css(col,a*0.85);
      ctx.beginPath();ctx.arc(px,py+p.vy*0.06,p.size*(1+t*0.6),0,TAU);ctx.fill();
      ctx.globalCompositeOperation="source-over";
    } else if(p.type==="smoke"||p.type==="steam"){
      ctx.fillStyle=css(col,a*0.34);
      ctx.beginPath();ctx.arc(px,py+p.vy*0.05,p.size*(1+t*1.5),0,TAU);ctx.fill();
    } else if(p.type==="angry"){
      ctx.fillStyle=css(col,a);ctx.font="bold 11px "+getComputedStyle(document.body).fontFamily;
      ctx.textAlign="center";ctx.fillText("!",px,py-18-t*10);ctx.textAlign="left";
    } else if(p.type==="drop"){
      ctx.strokeStyle=css(col,a*0.6);ctx.lineWidth=1.1;
      ctx.beginPath();ctx.moveTo(px,py);ctx.lineTo(px+WIND*2,py+5);ctx.stroke();
    } else {
      ctx.fillStyle=css(col,a);
      if(p.type==="leaf"||p.type==="petal"||p.type==="snowp"){
        ctx.save();ctx.translate(px,py);ctx.rotate(p.rot);
        ctx.beginPath();ctx.ellipse(0,0,p.size,p.size*0.5,0,0,TAU);ctx.fill();ctx.restore();
      } else {
        ctx.beginPath();ctx.arc(px,py,p.size,0,TAU);ctx.fill();
      }
    }
  }
}

/* ── lighting ─────────────────────────────────────────────────────────── */
const _lights=[];
function collectLights(vr){
  _lights.length=0;
  const night=1-dayLight();
  const fireActive=_fireSet.size>0;
  if(night<0.08&&!fireActive&&G.wx.lightning<=0)return;
  for(const b of G.buildings){
    if(!b||b.dead||b.built<1)continue;
    if(b.x>vr.x1+3||b.x+b.w<vr.x0-3||b.y>vr.y1+3||b.y+b.h<vr.y0-3)continue;
    const cx=b.x+b.w/2, cy=b.y+b.h/2;
    if(b.def==="bonfire"){_lights.push({x:cx,y:cy-0.35,r:5.4,c:[255,170,70],i:1.15,fl:1});}
    else if(b.def==="lamp"){_lights.push({x:cx,y:cy-0.55,r:3.6,c:[255,206,130],i:0.9,fl:0.5});}
    else if(night>0.25){
      if(b.def==="house")_lights.push({x:cx,y:cy-0.3,r:2.9,c:[255,196,116],i:0.55+night*0.4,fl:0.1});
      else if(b.def==="workshop")_lights.push({x:cx,y:cy-0.3,r:2.6,c:[255,178,96],i:0.42+night*0.32,fl:0.25});
      else if(b.def==="market")_lights.push({x:cx,y:cy-0.3,r:3.1,c:[255,214,150],i:0.4+night*0.35,fl:0.1});
      else if(b.def==="statue")_lights.push({x:cx,y:cy-0.6,r:3.4,c:[198,214,255],i:0.4+night*0.3,fl:0.05});
      else if(b.def==="infirm")_lights.push({x:cx,y:cy-0.3,r:2.6,c:[216,232,255],i:0.36+night*0.28,fl:0.05});
    }
  }
  for(const i of _fireSet){
    const f=G.fire[i]; if(!(f>0.02))continue;
    const x=i%MAP_W,y=(i/MAP_W)|0;
    if(x<vr.x0-2||x>vr.x1+2||y<vr.y0-2||y>vr.y1+2)continue;
    _lights.push({x:x+0.5,y:y+0.5,r:2.6+f*2.6,c:[255,140,50],i:0.6+f*0.7,fl:1.6});
  }
}
function drawLighting(time){
  const night=1-dayLight();
  if(night<0.06&&G.wx.lightning<=0&&_lights.length===0)return;
  if(!LIGHT_CV||LIGHT_CV.width<2)resizeLight();
  const s=LIGHT_CV.width/VW;
  LCTX.setTransform(1,0,0,1,0,0);
  LCTX.clearRect(0,0,LIGHT_CV.width,LIGHT_CV.height);
  LCTX.globalCompositeOperation="source-over";
  const d=clamp(night*0.88,0,0.9);
  if(d>0.01){
    const nc=mixRGB([10,14,34],[4,6,16],clamp(night*1.2,0,1));
    LCTX.fillStyle=css(nc,d);
    LCTX.fillRect(0,0,LIGHT_CV.width,LIGHT_CV.height);
    LCTX.globalCompositeOperation="destination-out";
    for(const l of _lights){
      const sp=toScreen(l.x,l.y);
      const rr=l.r*HW*G.cam.z*(1+Math.sin(time*(4+l.fl*7)+l.x)*0.05*l.fl);
      const cx=sp.x*s, cy=(sp.y-rr*0.25)*s, R=rr*s;
      if(!(R>0)||!isFinite(cx)||!isFinite(cy))continue;
      if(cx<-R||cx>LIGHT_CV.width+R||cy<-R||cy>LIGHT_CV.height+R)continue;
      const g=LCTX.createRadialGradient(cx,cy,0,cx,cy,R);
      g.addColorStop(0,"rgba(0,0,0,"+(0.96*l.i)+")");
      g.addColorStop(0.42,"rgba(0,0,0,"+(0.55*l.i)+")");
      g.addColorStop(1,"rgba(0,0,0,0)");
      LCTX.fillStyle=g;LCTX.beginPath();LCTX.arc(cx,cy,R,0,TAU);LCTX.fill();
    }
  }
  ctx.save();
  ctx.setTransform(DPR,0,0,DPR,0,0);
  ctx.globalCompositeOperation="source-over";
  ctx.drawImage(LIGHT_CV,0,0,VW,VH);
  // additive warm bloom
  ctx.globalCompositeOperation="lighter";
  for(const l of _lights){
    const sp=toScreen(l.x,l.y);
    const rr=l.r*HW*G.cam.z*(1+Math.sin(time*(4+l.fl*7)+l.x)*0.06*l.fl);
    if(!(rr>0)||!isFinite(sp.x)||!isFinite(sp.y))continue;
    if(sp.x<-rr||sp.x>VW+rr||sp.y<-rr||sp.y>VH+rr)continue;
    const g=ctx.createRadialGradient(sp.x,sp.y-rr*0.25,0,sp.x,sp.y-rr*0.25,rr);
    const inten=l.i*(0.20+night*0.42);
    g.addColorStop(0,css(l.c,inten));
    g.addColorStop(0.45,css(l.c,inten*0.34));
    g.addColorStop(1,css(l.c,0));
    ctx.fillStyle=g;ctx.beginPath();ctx.arc(sp.x,sp.y-rr*0.25,rr,0,TAU);ctx.fill();
  }
  if(G.wx.lightning>0){
    ctx.globalCompositeOperation="source-over";
    ctx.fillStyle=css([214,228,255],G.wx.lightning*0.42);
    ctx.fillRect(0,0,VW,VH);
  }
  ctx.restore();
}

/* ── weather overlay (screen space) ───────────────────────────────────── */
const _rain=[],_snow=[];
for(let i=0;i<260;i++)_rain.push({x:Math.random(),y:Math.random(),s:0.6+Math.random()*0.7,l:8+Math.random()*14});
for(let i=0;i<190;i++)_snow.push({x:Math.random(),y:Math.random(),s:0.6+Math.random()*1.1,p:Math.random()*TAU});
function drawWeatherScreen(time,dt){
  ctx.save();
  ctx.setTransform(DPR,0,0,DPR,0,0);
  const w=G.wx.type;
  if(w==="rain"||w==="storm"){
    const n=w==="storm"?260:170;
    ctx.strokeStyle=css([178,206,236],w==="storm"?0.34:0.24);
    ctx.lineWidth=1.1;
    ctx.beginPath();
    for(let i=0;i<n;i++){
      const d=_rain[i];
      d.y+=dt*(1.5+d.s*1.4); if(d.y>1){d.y-=1;d.x=Math.random();}
      const x=d.x*VW+WIND*40*d.s, y=d.y*VH;
      ctx.moveTo(x,y);ctx.lineTo(x-WIND*4.4*d.s,y+d.l*d.s);
    }
    ctx.stroke();
    ctx.fillStyle=css([40,58,80],w==="storm"?0.20:0.11);
    ctx.fillRect(0,0,VW,VH);
  } else if(w==="snow"){
    ctx.fillStyle=css([240,248,255],0.85);
    for(let i=0;i<170;i++){
      const d=_snow[i];
      d.y+=dt*(0.055+d.s*0.05); d.p+=dt*(1+d.s);
      if(d.y>1){d.y-=1;d.x=Math.random();}
      const x=(d.x+Math.sin(d.p)*0.014)*VW, y=d.y*VH;
      ctx.beginPath();ctx.arc(x,y,d.s*1.7,0,TAU);ctx.fill();
    }
    ctx.fillStyle=css([226,238,250],0.075);ctx.fillRect(0,0,VW,VH);
  } else if(w==="fog"){
    ctx.fillStyle=css([198,208,220],0.17);ctx.fillRect(0,0,VW,VH);
    for(let i=0;i<5;i++){
      const x=((time*7+i*340)%(VW+700))-350, y=VH*(0.18+i*0.17);
      const g=ctx.createRadialGradient(x,y,0,x,y,320);
      g.addColorStop(0,css([214,224,234],0.14));g.addColorStop(1,css([214,224,234],0));
      ctx.fillStyle=g;ctx.beginPath();ctx.arc(x,y,320,0,TAU);ctx.fill();
    }
  } else if(w==="clouds"){
    ctx.fillStyle=css([70,88,110],0.10);ctx.fillRect(0,0,VW,VH);
  }
  ctx.restore();
}

/* ── colour grade + vignette ──────────────────────────────────────────── */
function drawGrade(){
  ctx.save();ctx.setTransform(DPR,0,0,DPR,0,0);
  const S=SEASONS[G.season], nx=SEASONS[(G.season+1)%4];
  const bl=smooth(sat((G.seasonDay-(SEASON_DAYS-4))/4));
  const t=mixRGB(hex2rgb(S.col),hex2rgb(nx.col),bl);
  ctx.globalCompositeOperation="soft-light";
  ctx.fillStyle=css(t,0.30);ctx.fillRect(0,0,VW,VH);
  ctx.globalCompositeOperation="overlay";
  const A=ambience();
  if(A.warm>0.05){ctx.fillStyle=css([255,168,90],A.warm*0.16);ctx.fillRect(0,0,VW,VH);}
  ctx.globalCompositeOperation="source-over";
  const g=ctx.createRadialGradient(VW*0.5,VH*0.5,Math.min(VW,VH)*0.34,VW*0.5,VH*0.5,Math.max(VW,VH)*0.78);
  g.addColorStop(0,"rgba(0,0,0,0)");g.addColorStop(1,"rgba(0,0,0,"+(0.42+A.night*0.2)+")");
  ctx.fillStyle=g;ctx.fillRect(0,0,VW,VH);
  ctx.restore();
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 11 · scene composition, world overlays, minimap, camera
═══════════════════════════════════════════════════════════════════════════════*/

const _ents=[];
function collectEntities(vr){
  _ents.length=0;
  const x0=vr.x0-1,x1=vr.x1+1,y0=vr.y0-1,y1=vr.y1+1;
  // sprites rise from their base tile, so keep a tall margin below the bottom edge
  const ex0=vr.wx0-HW,ex1=vr.wx1+HW,ey0=vr.wy0-10,ey1=vr.wy1+86;
  const onScr=(px,cy)=>px>=ex0&&px<=ex1&&cy>=ey0&&cy<=ey1;
  for(let y=max(0,y0);y<min(MAP_H,y1);y++){
    for(let x=max(0,x0);x<min(MAP_W,x1);x++){
      const i=y*MAP_W+x;
      const rid=G.res[i], bid=G.bld[i];
      if(!rid&&!bid)continue;
      if(!onScr(isoX(x,y),isoY(x,y)))continue;
      if(rid){const n=G.nodes[rid];if(n&&!n.dead&&!n.hidden)_ents.push({d:x+y+0.5,k:0,o:n});}
      if(bid){const b=G.buildings[bid];
        if(b&&!b.dead&&b.x===x&&b.y===y&&b.def!=="road"&&b.def!=="farm")
          _ents.push({d:(b.x+b.w-1)+(b.y+b.h-1)+0.55,k:1,o:b});}
    }
  }
  for(const it of G.items){
    if(!it||it.dead)continue;
    if(it.x<x0||it.x>x1||it.y<y0||it.y>y1)continue;
    if(!onScr(isoX(it.x,it.y),isoY(it.x,it.y)))continue;
    _ents.push({d:it.x+it.y+0.2,k:2,o:it});
  }
  for(const a of G.animals){
    if(!a||a.dead)continue;
    if(a.x<x0||a.x>x1||a.y<y0||a.y>y1)continue;
    if(!onScr(isoX(a.x,a.y),isoY(a.x,a.y)))continue;
    _ents.push({d:a.x+a.y+0.42,k:5,o:a});
  }
  for(const c of G.cols){
    if(!c||!c.alive)continue;
    if(c.x<x0||c.x>x1||c.y<y0||c.y>y1)continue;
    if(!onScr(isoX(c.x,c.y),isoY(c.x,c.y)))continue;
    _ents.push({d:c.x+c.y+0.4,k:3,o:c});
  }
  for(const e of G.enemies){
    if(!e||e.dead)continue;
    if(e.x<x0||e.x>x1||e.y<y0||e.y>y1)continue;
    if(!onScr(isoX(e.x,e.y),isoY(e.x,e.y)))continue;
    _ents.push({d:e.x+e.y+0.45,k:4,o:e});
  }
  _ents.sort((a,b)=>a.d-b.d);
}
function drawEntities(time){
  for(const e of _ents){
    switch(e.k){
      case 0:{const n=e.o;drawNode(isoX(n.x+0.5,n.y+0.5),isoY(n.x+0.5,n.y+0.5),n,time);break;}
      case 1:{drawBuilding(e.o,time);break;}
      case 2:{drawItem(e.o,time);break;}
      case 3:{drawColonist(e.o,time);break;}
      case 4:{const en=e.o;if(en.kind==="wolf")drawWolf(en,time);else drawBandit(en,time);break;}
      case 5:{drawAnimal(e.o,time);break;}
    }
  }
}

/* ── world overlays ───────────────────────────────────────────────────── */
function drawWorldOverlays(time){
  // designation markers
  for(const e of _ents){
    if(e.k!==0)continue;
    const n=e.o;
    if(!n.marked)continue;
    const px=isoX(n.x+0.5,n.y+0.5),py=isoY(n.x+0.5,n.y+0.5);
    const col=n.kind<=3||n.kind===8?"#f2b45c":(n.kind===N.BUSH||n.kind===N.FLAX?"#5fd69b":"#9aa4b2");
    ctx.strokeStyle=col;ctx.lineWidth=1.8;
    ctx.globalAlpha=0.85;
    ctx.beginPath();ctx.moveTo(px-5,py-24);ctx.lineTo(px+5,py-14);ctx.moveTo(px+5,py-24);ctx.lineTo(px-5,py-14);ctx.stroke();
    ctx.globalAlpha=1;
  }
  // hover tile
  const hv=G.hoverTile;
  if(hv&&inb(hv.x,hv.y)&&!G.tool){
    const px=isoX(hv.x+0.5,hv.y+0.5),py=isoY(hv.x+0.5,hv.y+0.5);
    ctx.strokeStyle=css([255,255,255],0.30+Math.sin(time*4)*0.08);ctx.lineWidth=1.3;
    diamondPath(px,py);ctx.stroke();
  }
  // drag rect
  if(G.mouse.drag){
    const d=G.mouse.drag;
    const x0=min(d.x0,d.x1),x1=max(d.x0,d.x1),y0=min(d.y0,d.y1),y1=max(d.y0,d.y1);
    ctx.strokeStyle=css([255,220,140],0.9);ctx.lineWidth=1.8;
    ctx.beginPath();
    ctx.moveTo(isoX(x0,y0),isoY(x0,y0));ctx.lineTo(isoX(x1+1,y0),isoY(x1+1,y0));
    ctx.lineTo(isoX(x1+1,y1+1),isoY(x1+1,y1+1));ctx.lineTo(isoX(x0,y1+1),isoY(x0,y1+1));
    ctx.closePath();ctx.stroke();
    ctx.fillStyle=css([255,220,140],0.10);ctx.fill();
  }
  // build ghost
  if(G.tool&&BDEF[G.tool]&&hv){
    const key=G.tool,d=BDEF[key];
    const gx=d.w>1?hv.x-((d.w/2)|0):hv.x, gy=d.h>1?hv.y-((d.h/2)|0):hv.y;
    G.ghost={x:gx,y:gy};
    const chk=canPlace(key,gx,gy);
    ctx.globalAlpha=0.55;
    const fb={id:-1,def:key,x:gx,y:gy,w:d.w,h:d.h,built:1,hp:1,maxhp:1,quality:0,mats:{},seed:0,crop:"wheat",stage:0};
    drawBuilding(fb,time);
    ctx.globalAlpha=1;
    const col=chk.ok?[110,226,150]:[240,100,86];
    ctx.strokeStyle=css(col,0.95);ctx.lineWidth=2;
    ctx.beginPath();
    ctx.moveTo(isoX(gx,gy),isoY(gx,gy));ctx.lineTo(isoX(gx+d.w,gy),isoY(gx+d.w,gy));
    ctx.lineTo(isoX(gx+d.w,gy+d.h),isoY(gx+d.w,gy+d.h));ctx.lineTo(isoX(gx,gy+d.h),isoY(gx,gy+d.h));
    ctx.closePath();ctx.stroke();
    ctx.fillStyle=css(col,0.13);ctx.fill();
    // radius preview
    if(d.mood||d.light||d.militia){
      const rr=(d.mood?5.5:(d.light?4.2:7.5));
      ctx.strokeStyle=css(col,0.28);ctx.lineWidth=1.2;ctx.setLineDash([5,5]);
      ctx.beginPath();ctx.ellipse(isoX(gx+d.w/2,gy+d.h/2),isoY(gx+d.w/2,gy+d.h/2),rr*HW,rr*HH,0,0,TAU);ctx.stroke();
      ctx.setLineDash([]);
    }
    if(!chk.ok){
      const gpx=isoX(gx+d.w/2,gy+d.h/2), gpy=isoY(gx+d.w/2,gy+d.h/2);
      ctx.font="600 "+(11/G.cam.z)+"px "+getComputedStyle(document.body).fontFamily;
      ctx.textAlign="center";
      const w=ctx.measureText(chk.why).width/G.cam.z+12/G.cam.z;
      ctx.fillStyle=css([12,8,8],0.82);
      roundRect(gpx-w/2,gpy-30/G.cam.z,w,17/G.cam.z,5/G.cam.z);ctx.fill();
      ctx.fillStyle=css([255,168,154],0.98);
      ctx.fillText(chk.why,gpx,gpy-18/G.cam.z);
      ctx.textAlign="left";
    }
  }
  // selection
  if(G.sel){
    if(G.sel.type==="col"){
      const c=G.cols[G.sel.id];
      if(c&&c.alive&&c.path){
        ctx.strokeStyle=css([242,180,92],0.35);ctx.lineWidth=1.4;ctx.setLineDash([3,4]);
        ctx.beginPath();
        for(let k=c.pi;k<c.path.length;k++){
          const t=c.path[k],tx=t%MAP_W,ty=(t/MAP_W)|0;
          const px=isoX(tx+0.5,ty+0.5),py=isoY(tx+0.5,ty+0.5);
          if(k===c.pi)ctx.moveTo(px,py);else ctx.lineTo(px,py);
        }
        ctx.stroke();ctx.setLineDash([]);
      }
    } else if(G.sel.type==="bld"){
      const b=G.buildings[G.sel.id];
      if(b&&!b.dead){
        const d=BDEF[b.def];
        const pulse=0.55+Math.sin(time*4)*0.22;
        ctx.strokeStyle=css([242,180,92],pulse);ctx.lineWidth=2;
        ctx.beginPath();
        ctx.moveTo(isoX(b.x,b.y),isoY(b.x,b.y));ctx.lineTo(isoX(b.x+b.w,b.y),isoY(b.x+b.w,b.y));
        ctx.lineTo(isoX(b.x+b.w,b.y+b.h),isoY(b.x+b.w,b.y+b.h));ctx.lineTo(isoX(b.x,b.y+b.h),isoY(b.x,b.y+b.h));
        ctx.closePath();ctx.stroke();
        if(d.mood||d.light||d.militia){
          const rr=(d.mood?5.5:(d.light?4.2:7.5));
          ctx.strokeStyle=css([242,180,92],0.22);ctx.lineWidth=1.2;ctx.setLineDash([5,5]);
          ctx.beginPath();ctx.ellipse(isoX(b.x+b.w/2,b.y+b.h/2),isoY(b.x+b.w/2,b.y+b.h/2),rr*HW,rr*HH,0,0,TAU);ctx.stroke();
          ctx.setLineDash([]);
        }
      }
    } else if(G.sel.type==="node"){
      const n=G.nodes[G.sel.id];
      if(n&&!n.dead){
        ctx.strokeStyle=css([120,220,160],0.75);ctx.lineWidth=1.8;
        ctx.beginPath();ctx.ellipse(isoX(n.x+0.5,n.y+0.5),isoY(n.x+0.5,n.y+0.5),14,7,0,0,TAU);ctx.stroke();
      }
    }
  }
  // camp drop-off marker
  if(G.camp&&!G.buildings.some(b=>b&&!b.dead&&b.built>=1&&BDEF[b.def].store)){
    const px=isoX(G.camp.x+0.5,G.camp.y+0.5),py=isoY(G.camp.x+0.5,G.camp.y+0.5);
    const a=0.32+Math.sin(time*2.4)*0.14;
    ctx.strokeStyle=css([242,180,92],a);ctx.lineWidth=1.4;ctx.setLineDash([4,4]);
    ctx.beginPath();ctx.ellipse(px,py,HW*0.9,HH*0.9,0,0,TAU);ctx.stroke();ctx.setLineDash([]);
    ctx.fillStyle=css([242,180,92],a+0.2);
    ctx.font="600 9px "+getComputedStyle(document.body).fontFamily;ctx.textAlign="center";
    ctx.fillText("depósito",px,py+3);ctx.textAlign="left";
  }
}

/* ── floating texts (screen space) ────────────────────────────────────── */
function drawFloats(){
  if(!G.floats.length)return;
  ctx.save();ctx.setTransform(DPR,0,0,DPR,0,0);
  ctx.textAlign="center";
  for(const f of G.floats){
    const sp=toScreen(f.x,f.y);
    if(sp.x<-80||sp.x>VW+80||sp.y<-40||sp.y>VH+40)continue;
    const t=1-f.life/f.max;
    const a=t<0.15?t/0.15:(f.life<0.5?f.life/0.5:1);
    ctx.font="600 "+(11.5*G.cam.z>13?13:11.5*max(0.8,G.cam.z)).toFixed(1)+"px "+getComputedStyle(document.body).fontFamily;
    ctx.lineWidth=3;ctx.strokeStyle=css([6,8,14],a*0.85);
    ctx.strokeText(f.txt,sp.x,sp.y-26-t*16);
    ctx.fillStyle=css(hex2rgb(f.col[0]==="#"?f.col:"#ffffff"),a);
    ctx.fillText(f.txt,sp.x,sp.y-26-t*16);
  }
  ctx.textAlign="left";
  ctx.restore();
}
/* name tags for hovered unit */
function drawTags(){
  if(!G.hoverUnit)return;
  const u=G.hoverUnit;
  const nm=u.name||(u.kind==="wolf"?"Lobo":(NODEDEF[u.kind]?NODEDEF[u.kind].name:null));
  if(!nm)return;
  const sp=toScreen(u.x+(u.w?u.w/2:0.5),u.y+(u.h?u.h/2:0.5));
  ctx.save();ctx.setTransform(DPR,0,0,DPR,0,0);
  ctx.font="600 11px "+getComputedStyle(document.body).fontFamily;
  const w=ctx.measureText(nm).width+14;
  ctx.fillStyle=css([10,13,20],0.85);
  roundRect(sp.x-w/2,sp.y-46,w,17,6);ctx.fill();
  ctx.strokeStyle=css([255,255,255],0.14);ctx.lineWidth=1;ctx.stroke();
  ctx.fillStyle=css([232,238,248],0.95);ctx.textAlign="center";
  ctx.fillText(nm,sp.x,sp.y-34);ctx.textAlign="left";
  ctx.restore();
}

/* ── minimap ──────────────────────────────────────────────────────────── */
let MM=null,MMCTX=null,MM_S=1,MM_OX=0,MM_OY=0;
function buildMinimapBase(){
  const c=$("#minimap");
  if(!c)return;
  MM=document.createElement("canvas");MM.width=MAP_W;MM.height=MAP_H;MMCTX=MM.getContext("2d");
  const img=MMCTX.createImageData(MAP_W,MAP_H);
  for(let y=0;y<MAP_H;y++)for(let x=0;x<MAP_W;x++){
    const i=y*MAP_W+x, b=G.bio[i];
    let col=BIOME_COL[b][0].slice();
    const v=G.tv?G.tv[i]:0;
    col[0]=clamp(col[0]+v*16+G.hgt[i]*4,0,255);
    col[1]=clamp(col[1]+v*18+G.hgt[i]*4,0,255);
    col[2]=clamp(col[2]+v*12+G.hgt[i]*5,0,255);
    const o=(y*MAP_W+x)*4;
    img.data[o]=col[0];img.data[o+1]=col[1];img.data[o+2]=col[2];img.data[o+3]=255;
  }
  MMCTX.putImageData(img,0,0);
  const cv2=$("#minimap");
  MM_S=min(cv2.width/MAP_W,cv2.height/MAP_H);
  MM_OX=(cv2.width-MAP_W*MM_S)/2; MM_OY=(cv2.height-MAP_H*MM_S)/2;
}
let _mmT=0;
function drawMinimap(time,dt){
  const c=$("#minimap"); if(!c||!MM)return;
  _mmT-=dt; 
  const g=c.getContext("2d");
  g.setTransform(1,0,0,1,0,0);
  g.fillStyle="#080b11";g.fillRect(0,0,c.width,c.height);
  g.imageSmoothingEnabled=true;
  g.drawImage(MM,MM_OX,MM_OY,MAP_W*MM_S,MAP_H*MM_S);
  if(_mmT>0){return;}
  _mmT=0.12;
  const S=0.5;
  // buildings
  for(const b of G.buildings){
    if(!b||b.dead)continue;
    if(b.def==="road"){g.fillStyle="rgba(190,170,130,.55)";}
    else if(b.built<1){g.fillStyle="rgba(255,214,140,.75)";}
    else g.fillStyle="rgba(242,180,92,.95)";
    g.fillRect(MM_OX+b.x*MM_S,MM_OY+b.y*MM_S,max(1.2,b.w*MM_S),max(1.2,b.h*MM_S));
  }
  // fire
  for(let i=0;i<G.fire.length;i++){
    if(G.fire[i]>0.1){
      g.fillStyle="rgba(255,90,40,.95)";
      g.fillRect(MM_OX+(i%MAP_W)*MM_S,MM_OY+((i/MAP_W)|0)*MM_S,2,2);
    }
  }
  // units
  for(const col of G.cols){if(!col||!col.alive)continue;
    g.fillStyle="#eaf2ff";g.fillRect(MM_OX+col.x*MM_S-1,MM_OY+col.y*MM_S-1,2.4,2.4);}
  for(const e of G.enemies){if(e.dead)continue;
    g.fillStyle="#ff5a48";g.fillRect(MM_OX+e.x*MM_S-1.2,MM_OY+e.y*MM_S-1.2,3,3);}
  // viewport rect
  const tl=toTile(0,0),br=toTile(VW,VH);
  g.strokeStyle="rgba(255,255,255,.5)";g.lineWidth=1;
  g.strokeRect(MM_OX+tl.x*MM_S,MM_OY+tl.y*MM_S,(br.x-tl.x)*MM_S,(br.y-tl.y)*MM_S);
  $("#mapScale").textContent=round(G.cam.z*100)+"%";
}

/* ── camera ───────────────────────────────────────────────────────────── */
function clampCam(){
  const lim=MAP_W*HW*G.cam.z*0.62+VW*0.35;
  const limy=MAP_H*HH*G.cam.z*0.62+VH*0.35;
  G.cam.x=clamp(G.cam.x,-lim,lim);
  G.cam.y=clamp(G.cam.y,-limy,limy);
}
function updateCamera(dt){
  const sp=760*dt/G.cam.z;
  let dx=0,dy=0;
  if(keys["w"]||keys["arrowup"])dy+=sp;
  if(keys["s"]||keys["arrowdown"])dy-=sp;
  if(keys["a"]||keys["arrowleft"])dx+=sp;
  if(keys["d"]||keys["arrowright"])dx-=sp;
  if(dx||dy){G.cam.x+=dx;G.cam.y+=dy;G.cam.vx=dx*4;G.cam.vy=dy*4;clampCam();}
  else {
    G.cam.x+=G.cam.vx*dt;G.cam.y+=G.cam.vy*dt;
    G.cam.vx*=Math.pow(0.0016,dt);G.cam.vy*=Math.pow(0.0016,dt);
    clampCam();
  }
  const t=toTile(VW*0.5,VH*0.5);
  G.cam.tx=clamp(t.x,0,MAP_W);G.cam.ty=clamp(t.y,0,MAP_H);
}
function zoomAt(mx,my,f){
  const z0=G.cam.z,z1=clamp(z0*f,0.34,3.4);
  if(z1===z0)return;
  const k=z1/z0;
  G.cam.x=mx-VW*0.5-(mx-VW*0.5-G.cam.x)*k;
  G.cam.y=my-VH*0.5-(my-VH*0.5-G.cam.y)*k;
  G.cam.z=z1;clampCam();
}
function centerOn(x,y,instant){
  if(x==null||y==null){
    if(!G.camp)return;
    x=G.camp.x;y=G.camp.y;
  }
  G.cam.x=-(isoX(x,y)*G.cam.z);
  G.cam.y=-(isoY(x,y)*G.cam.z);
  clampCam();
}

/* ── main render ──────────────────────────────────────────────────────── */
function render(time,dt){
  updatePalette();
  const A=ambience();
  AMB=0.33+A.L*0.75; WARM=A.warm*0.5; NIGHT=A.night;

  ctx.setTransform(DPR,0,0,DPR,0,0);
  // sky / void
  const sky=skyTop();
  const sg=ctx.createLinearGradient(0,0,0,VH);
  sg.addColorStop(0,css(shade(sky,0.55)));
  sg.addColorStop(1,css(shade(sky,0.22)));
  ctx.fillStyle=sg;ctx.fillRect(0,0,VW,VH);

  ctx.save();
  ctx.translate(VW*0.5+G.cam.x,VH*0.5+G.cam.y);
  ctx.scale(G.cam.z,G.cam.z);

  const vr=visibleRange();
  drawTerrain(vr,time);
  drawOverlay(vr,time);
  collectEntities(vr);
  drawEntities(time);
  collectLights(vr);
  drawParticles();
  drawWorldOverlays(time);

  ctx.restore();

  drawLighting(time);
  drawWeatherScreen(time,dt);
  drawGrade();
  drawFloats();
  drawTags();
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 12 · input, interface, save/load, main loop
═══════════════════════════════════════════════════════════════════════════════*/

const keys={};
let panMode=false,panStart=null,camStart=null;

/* ── designation ──────────────────────────────────────────────────────── */
function markNode(n,type){
  if(n.marked)return false;
  n.marked=true;
  addJob({type,x:n.x,y:n.y,node:n.id,prio:4,work:NODEDEF[n.kind].work,skill:SKILL_OF[type]});
  return true;
}
function unmarkNode(n){
  if(!n.marked)return;
  n.marked=false;
  killJobsFor(j=>j.node===n.id&&(j.type==="chop"||j.type==="mine"||j.type==="gather"));
}
function applyDesignation(x0,y0,x1,y1){
  const t=G.tool; if(!t||!TOOLS[t])return;
  let count=0;
  for(let y=min(y0,y1);y<=max(y0,y1);y++)for(let x=min(x0,x1);x<=max(x0,x1);x++){
    if(!inb(x,y))continue;
    const i=idx(x,y);
    const rid=G.res[i], bid=G.bld[i];
    if(t==="cancel"){
      if(rid){const n=G.nodes[rid];if(n&&!n.dead){unmarkNode(n);count++;}}
      if(bid){const b=G.buildings[bid];if(b&&!b.dead){killJobsFor(j=>j.bx===b.id&&j.type==="build");count++;}}
      continue;
    }
    if(t==="demo"){
      if(bid){const b=G.buildings[bid];
        if(b&&!b.dead&&!jobAt(b.x,b.y,"clear")){addJob({type:"clear",x:b.x,y:b.y,bx:b.id,prio:6,work:2});count++;}}
      else if(rid){const n=G.nodes[rid];
        if(n&&!n.dead&&!jobAt(n.x,n.y,"clear")){addJob({type:"clear",x:n.x,y:n.y,node:n.id,prio:6,work:1.4});count++;}}
      else if(G.ovr[i]===O.ROAD){G.ovr[i]=O.NONE;recomputeCostLocal(x,y);count++;}
      continue;
    }
    if(!rid)continue;
    const n=G.nodes[rid];
    if(!n||n.dead||n.hidden||n.marked)continue;
    const k=n.kind;
    if(t==="chop"&&(k===N.OAK||k===N.PINE||k===N.BIRCH||k===N.DEADTREE))count+=markNode(n,"chop")?1:0;
    else if(t==="mine"&&(k===N.BOULDER||k===N.ORE))count+=markNode(n,"mine")?1:0;
    else if(t==="gather"&&(k===N.BUSH||k===N.FLAX))count+=markNode(n,"gather")?1:0;
  }
  if(count>0){
    Audio_.ui();
    hint(count+" "+(t==="demo"?"demolições marcadas":t==="cancel"?"ordens canceladas":"ordens emitidas"));
  } else Audio_.err();
}

/* ── picking ──────────────────────────────────────────────────────────── */
function pickAt(tx,ty){
  // colonists first (nearest to click point)
  let best=null,bd=0.75;
  for(const c of G.cols){
    if(!c||!c.alive)continue;
    const d=Math.hypot(c.x-(tx+0.5),c.y-(ty+0.5));
    if(d<bd){bd=d;best={type:"col",id:c.id};}
  }
  if(best)return best;
  for(const e of G.enemies){
    if(e.dead)continue;
    if(Math.hypot(e.x-(tx+0.5),e.y-(ty+0.5))<0.8)return {type:"enemy",id:e.id};
  }
  for(const a of G.animals){
    if(a.dead)continue;
    if(Math.hypot(a.x-(tx+0.5),a.y-(ty+0.5))<0.8)return {type:"animal",id:a.id};
  }
  if(!inb(tx,ty))return null;
  const i=idx(tx,ty);
  if(G.bld[i]){const b=G.buildings[G.bld[i]];if(b&&!b.dead)return {type:"bld",id:b.id};}
  if(G.res[i]){const n=G.nodes[G.res[i]];if(n&&!n.dead)return {type:"node",id:n.id};}
  for(const it of G.items){if(!it.dead&&it.x===tx&&it.y===ty)return {type:"item",id:it.id};}
  return {type:"tile",x:tx,y:ty};
}
function unitAtMouse(mx,my){
  const t=toTile(mx,my);
  let best=null,bd=0.8;
  for(const c of G.cols){if(!c||!c.alive)continue;const d=Math.hypot(c.x-t.x,c.y-t.y);if(d<bd){bd=d;best=c;}}
  if(best)return best;
  for(const e of G.enemies){if(e.dead)continue;const d=Math.hypot(e.x-t.x,e.y-t.y);if(d<bd){bd=d;best=e;}}
  if(best)return best;
  for(const a of G.animals){if(a.dead)continue;const d=Math.hypot(a.x-t.x,a.y-t.y);if(d<bd){bd=d;best=a;}}
  return best;
}

/* ── pointer input ────────────────────────────────────────────────────── */
on(cv,"pointermove",e=>{
  G.mouse.x=e.clientX;G.mouse.y=e.clientY;
  const t=toTile(e.clientX,e.clientY);
  G.hoverTile={x:floor(t.x),y:floor(t.y)};
  G.hoverUnit=(!G.tool)?unitAtMouse(e.clientX,e.clientY):null;
  if(G.mouse.drag){G.mouse.drag.x1=floor(t.x);G.mouse.drag.y1=floor(t.y);}
  if(panMode&&panStart){
    G.cam.x=camStart.x+(e.clientX-panStart.x);
    G.cam.y=camStart.y+(e.clientY-panStart.y);
    clampCam();
  }
});
on(cv,"pointerdown",e=>{
  Audio_.init();
  cv.setPointerCapture&&cv.setPointerCapture(e.pointerId);
  if(e.button===1||e.button===2||(e.button===0&&(keys[" "]||keys.shift))){
    panMode=true;panStart={x:e.clientX,y:e.clientY};camStart={x:G.cam.x,y:G.cam.y};
    e.preventDefault();return;
  }
  if(e.button!==0)return;
  const t=toTile(e.clientX,e.clientY);
  const tx=floor(t.x),ty=floor(t.y);
  if(G.tool&&TOOLS[G.tool]&&TOOLS[G.tool].drag){
    G.mouse.drag={x0:tx,y0:ty,x1:tx,y1:ty};
    return;
  }
  if(G.tool&&BDEF[G.tool]){
    const d=BDEF[G.tool];
    const gx=d.w>1?tx-((d.w/2)|0):tx, gy=d.h>1?ty-((d.h/2)|0):ty;
    if(canPlace(G.tool,gx,gy).ok){
      placeBuilding(G.tool,gx,gy);
      if(!keys.control)keepTool();
      else setTool(null);
    } else {
      const c=canPlace(G.tool,gx,gy);
      hint("<b>Não é possível:</b> "+c.why);
      Audio_.err();
    }
    return;
  }
  const sel=pickAt(tx,ty);
  G.sel=sel;
  setRP(sel&&sel.type==="col"?"col":"insp");
  renderSelBar();renderRight();
  if(sel&&sel.type!=="tile")Audio_.ui();
});
on(window,"pointerup",e=>{
  if(panMode){panMode=false;return;}
  if(G.mouse.drag){
    const d=G.mouse.drag;G.mouse.drag=null;
    applyDesignation(d.x0,d.y0,d.x1,d.y1);
  }
});
on(cv,"contextmenu",e=>{e.preventDefault();setTool(null);G.sel=null;renderSelBar();});
on(cv,"wheel",e=>{
  e.preventDefault();
  zoomAt(e.clientX,e.clientY,e.deltaY<0?1.14:1/1.14);
},{passive:false});
function keepTool(){/* sticky unless ctrl */}

/* ── keyboard ─────────────────────────────────────────────────────────── */
on(window,"keydown",e=>{
  const k=e.key.toLowerCase();
  keys[k]=true;
  if(e.key==="Control")keys.control=true;
  const inField=e.target&&(e.target.tagName==="INPUT"||e.target.tagName==="TEXTAREA");
  if(!G.started&&!inField&&$("#title")&&!$("#title").classList.contains("out")){
    if(/^[1-4]$/.test(e.key)){setMode(MODEORDER[+e.key-1]);Audio_.init();Audio_.ui();e.preventDefault();return;}
  }
  if($("#modalwrap").classList.contains("on")&&k==="escape"){closeModal();return;}
  if(k===" "){e.preventDefault();togglePause();return;}
  if(k==="escape"){setTool(null);G.sel=null;renderSelBar();return;}
  if(k==="h"){openHelp();return;}
  if(k==="m"){toggleSound();return;}
  if(k==="o"&&G.started){
    if($("#modalwrap").classList.contains("on")&&$("#mTitle").textContent==="Objetivos"){closeModal();return;}
    const rp=$("#rightpanel");
    if(rp&&rp.offsetParent!==null&&rpTab==="obj"){setRP("col");return;}
    openObjectives(); Audio_.ui(); return;
  }
  if(k===","||k==="-"){cycleSpeed(-1);return;}
  if(k==="."||k==="+"||k==="="){cycleSpeed(1);return;}
  if(k==="f"&&!G.tool){}
  for(const t of TOOLORDER)if(TOOLS[t].key===k){setTool(t);return;}
  for(const b of BORDER)if(BDEF[b].key.toLowerCase()===k){
    if(BDEF[b].pres&&!G.unlocked[b]){openObjectives();Audio_.err();return;}
    else setTool(b);
    return;
  }
  if(k==="tab"){e.preventDefault();cycleRP();return;}
  if(k==="enter"&&G.market.here)openTrade();
});
on(window,"keyup",e=>{
  const k=e.key.toLowerCase();keys[k]=false;
  if(e.key==="Control")keys.control=false;
});

/* ── tool / selection helpers ─────────────────────────────────────────── */
function setTool(t){
  G.tool=t;
  $$(".bitem").forEach(e=>e.classList.toggle("on",e.dataset.k===t));
  if(t){
    const d=BDEF[t]||TOOLS[t];
    hint("<b>"+d.name+"</b> — "+(TOOLS[t]&&TOOLS[t].drag?"arraste sobre o mapa":"clique para posicionar")+" · <b>Esc</b> cancela");
    Audio_.ui();
  } else $("#hint").classList.remove("on");
  renderSelBar();
}
let _hintT=null;
function hint(html){
  const h=$("#hint");h.innerHTML=html;h.classList.add("on");
  clearTimeout(_hintT);_hintT=setTimeout(()=>h.classList.remove("on"),3600);
}

/* ── HUD ──────────────────────────────────────────────────────────────── */
function buildResBar(){
  const bar=$("#resbar");bar.innerHTML="";
  for(const r of RESDEF){
    const e=el("div","res");
    e.dataset.k=r.k;
    e.innerHTML=ICONS[r.icon]+'<span class="v">0</span><span class="d"></span>';
    e.addEventListener("mouseenter",ev=>{
      const cap=r.k==="coin"?"—":fmt(storageCap());
      tipShow(`<b>${r.name}</b><p>${({wood:"Cortada das florestas. Base de quase toda construção.",
        stone:"Extraída de rochedos e minas. Muros, alicerces e ferramentas.",
        food:"Bagas, colheitas e caça. Cada colono come várias vezes por dia.",
        cloth:"Linho cultivado ou peles. Agasalhos contra o inverno.",
        tools:"Feitas na oficina. Colonos equipados trabalham 30% mais rápido.",
        coin:"Usada com caravanas. Gerada por impostos no mercado e veios ricos."})[r.k]}</p>
        <div class="tkv"><span>Em estoque</span><b>${fmt(G.stock[r.k])}</b></div>
        ${r.k==="coin"?"":`<div class="tkv"><span>Capacidade total</span><b>${cap}</b></div>`}
        <div class="tkv"><span>Preço de compra</span><b>${r.k==="coin"?"—":G.prices[r.k]?G.prices[r.k].buy.toFixed(1):"—"}</b></div>`,ev);
    });
    e.addEventListener("mouseleave",tipHide);
    bar.appendChild(e);
  }
}
let _lastRes={};
function updateHUD(dt){
  // clock
  const h=(G.t.min/60)%24, hh=floor(h), mm=floor((h-hh)*60);
  $("#dateTxt").textContent="Dia "+(G.seasonDay+1)+" · Ano "+G.year;
  $("#seasonTxt").innerHTML=SEASONS[G.season].name+" · "+String(hh).padStart(2,"0")+":"+String(mm).padStart(2,"0")+" · "+round(G.temp)+"°C · "+WEATHER[G.wx.type].name;
  $("#hourLbl").textContent=hh+"h";
  const prog=(G.t.min%DAY_MIN)/DAY_MIN;
  $("#ringArc").setAttribute("stroke-dashoffset",String(88*(1-prog)));
  $("#ringArc").setAttribute("stroke",isNight()?"#7f9fd6":"#f2b45c");
  // resources
  for(const r of RESDEF){
    const e=$('.res[data-k="'+r.k+'"]');if(!e)continue;
    const v=G.stock[r.k]|0;
    if(_lastRes[r.k]!==v){
      e.querySelector(".v").textContent=fmt(v);
      e.classList.remove("flash","neg");void e.offsetWidth;
      e.classList.add(v>(_lastRes[r.k]||0)?"flash":"neg");
      _lastRes[r.k]=v;
    }
    const d=e.querySelector(".d");
    if(r.k==="coin"){d.textContent="";}
    else{
      const f=G.flow[r.k]||0;
      d.textContent=f===0?"":sgn(f);
      d.className="d "+(f>0?"up":(f<0?"dn":""));
    }
  }
  // storage warning tint
  const st=stockTotal(),cap=storageCap();
  const woodE=$('.res[data-k="wood"]');
  if(woodE)woodE.style.borderColor=st>=cap?"rgba(240,104,90,.5)":"transparent";
  // minimap footer
  $("#mfPop").textContent=aliveCols().length+" colonos · "+G.jobs.filter(j=>!j.dead&&!j.by).length+" tarefas";
  $("#mfJobs").textContent="abrigo "+aliveCols().length+"/"+G.housingCap;
}
function cycleSpeed(d){
  if(G.t.paused&&d>0){G.t.paused=false;G.t.speed=1;}
  else {G.t.speed=clamp(G.t.speed+d,1,3);G.t.paused=false;}
  syncSpeedUI();Audio_.ui();
}
function togglePause(){
  G.t.paused=!G.t.paused;syncSpeedUI();Audio_.ui();
}
function syncSpeedUI(){
  for(let i=0;i<4;i++){
    const b=$("#sp"+i);if(!b)continue;
    const on=(i===0)?G.t.paused:(!G.t.paused&&G.t.speed===i);
    b.classList.toggle("on",on);
  }
}
for(let i=0;i<4;i++){const b=$("#sp"+i);if(b)b.addEventListener("click",()=>{
  if(i===0){G.t.paused=!G.t.paused;}else{G.t.paused=false;G.t.speed=i;}
  syncSpeedUI();Audio_.init();Audio_.ui();
});}

/* ── tooltips ─────────────────────────────────────────────────────────── */
const tip=$("#tip");
function tipShow(html,e){
  tip.innerHTML=html;tip.classList.add("on");
  tipMove(e);
}
function tipMove(e){
  if(!e)return;
  const r=tip.getBoundingClientRect();
  let x=e.clientX+16,y=e.clientY+14;
  if(x+r.width>VW-8)x=e.clientX-r.width-14;
  if(y+r.height>VH-8)y=VH-r.height-8;
  tip.style.left=x+"px";tip.style.top=y+"px";
}
function tipHide(){tip.classList.remove("on");}
on(window,"mousemove",e=>{if(tip.classList.contains("on"))tipMove(e);});

/* ── notifications & banner ───────────────────────────────────────────── */
function notify(title,text,kind){
  const log=$("#log");
  const t=el("div","toast "+(kind||"info"));
  const ico={good:"✓",bad:"!",info:"i",epic:"★"}[kind||"info"];
  const colr={good:"#5fd69b",bad:"#f0685a",info:"#63a9ef",epic:"#a98bf0"}[kind||"info"];
  t.innerHTML='<div class="tic" style="background:'+colr+'22;color:'+colr+'">'+ico+'</div><div class="tx"><b></b><p></p></div>';
  t.querySelector("b").textContent=title;
  t.querySelector("p").textContent=text||"";
  log.appendChild(t);
  while(log.children.length>5)log.removeChild(log.firstChild);
  setTimeout(()=>{t.classList.add("out");setTimeout(()=>t.remove(),420);},kind==="epic"?9000:6200);
}
let _banT=null;
function banner(title,sub){
  const b=$("#banner");
  $("#banT").textContent=title;$("#banS").textContent=sub||"";
  b.classList.add("on");
  clearTimeout(_banT);_banT=setTimeout(()=>b.classList.remove("on"),3200);
}

/* ── build menu ───────────────────────────────────────────────────────── */
let bmCat="ordem";
function buildMenu(){
  const tabs=$("#bmtabs");tabs.innerHTML="";
  for(const c of CATS){
    const b=el("button","bmtab"+(c.id===bmCat?" on":""),c.name);
    b.dataset.cat=c.id;
    b.onclick=()=>{bmCat=c.id;buildMenu();Audio_.ui();};
    tabs.appendChild(b);
  }
  const list=$("#bmlist");list.innerHTML="";
  const entries=[];
  if(bmCat==="ordem")for(const k of TOOLORDER)entries.push({kind:"tool",k,d:TOOLS[k]});
  else for(const k of BORDER)if(BDEF[k].cat===bmCat)entries.push({kind:"bld",k,d:BDEF[k]});
  for(const en of entries){
    const it=el("div","bitem"+(G.tool===en.k?" on":""));
    it.dataset.k=en.k;
    const locked=en.kind==="bld"&&en.d.pres&&!G.unlocked[en.k];
    const affordable=locked?false:(en.kind==="bld"?canAfford(en.d.cost):true);
    if(!affordable)it.classList.add("off");
    if(locked)it.classList.add("lock");
    let costHtml="";
    if(en.kind==="bld")for(const k in en.d.cost){
      const r=RESDEF.find(x=>x.k===k);
      costHtml+='<i style="--c:'+r.col+'" class="'+((G.stock[k]|0)<en.d.cost[k]?"no":"")+'">'+en.d.cost[k]+"</i>";
    }
    it.innerHTML='<div class="ico"><canvas width="92" height="80"></canvas></div><div class="meta">'+
      '<div class="nm">'+en.d.name+' <kbd>'+en.d.key.toUpperCase()+'</kbd></div>'+
      (locked?'<div class="pres">✦ '+en.d.pres+' de prestígio · tecla O</div>':"")+
      (costHtml?'<div class="cost">'+costHtml+"</div>":"")+
      '<div class="desc">'+en.d.desc+'</div></div>';
    it.onclick=()=>{
      if(locked){openObjectives();return;}
      setTool(G.tool===en.k?null:en.k);buildMenu();
    };
    it.addEventListener("mouseenter",ev=>{
      let extra="";
      if(en.kind==="bld"){
        const d=en.d;
        const rows=[];
        if(d.beds)rows.push(["Abrigo","+"+d.beds+" colonos"]);
        if(d.store)rows.push(["Capacidade","+"+d.store]);
        if(d.mood)rows.push(["Humor","+"+d.mood+" num raio de 5"]);
        if(d.light)rows.push(["Iluminação","raio "+(d.light/32).toFixed(1)+" tiles"]);
        if(d.militia)rows.push(["Milícia","+"+d.militia+" postos"]);
        if(d.hp)rows.push(["Durabilidade",d.hp]);
        if(d.soil)rows.push(["Requer","solo com fertilidade ≥ 22"]);
        if(d.near==="rock")rows.push(["Requer","rochedo adjacente"]);
        rows.push(["Tempo de obra",round(d.cost?Object.values(d.cost).reduce((a,c)=>a+c,0)*0.42:3)+"s de trabalho"]);
        extra=rows.map(r=>'<div class="tkv"><span>'+r[0]+'</span><b>'+r[1]+"</b></div>").join("");
      }
      tipShow("<b>"+en.d.name+"</b><p>"+en.d.desc+"</p>"+extra,ev);
    });
    it.addEventListener("mouseleave",tipHide);
    list.appendChild(it);
    renderIcon(it.querySelector("canvas"),en.kind==="tool"?"tool":"bld",en.k);
  }
}
function renderIcon(cvs,kind,key){
  const g=cvs.getContext("2d");
  const w=cvs.width,h=cvs.height;
  g.setTransform(1,0,0,1,0,0);g.clearRect(0,0,w,h);
  const real=ctx, ra=AMB, rw=WARM, rn=NIGHT, rf=NOFX;
  ctx=g;AMB=1.06;WARM=0.06;NIGHT=0;NOFX=true;
  g.save();
  try{
    if(kind==="bld"){
      const d=BDEF[key];
      g.translate(w/2-isoX(d.w/2,d.h/2),h*0.80-isoY(d.w/2,d.h/2));
      const fb={id:-1,def:key,x:0,y:0,w:d.w,h:d.h,built:1,hp:1,maxhp:1,quality:key==="house"?1:0,mats:{},seed:0,crop:"wheat",stage:0,maturity:0.8};
      drawBuilding(fb,0.4);
    } else {
      g.translate(w/2-isoX(0.5,0.5),h*0.84-isoY(0.5,0.5));
      if(key==="chop")drawNode(isoX(0.5,0.5),isoY(0.5,0.5),{kind:N.OAK,scale:0.95,variant:0,seed:1,growth:1,amount:5,hidden:false,marked:false},0.3);
      else if(key==="mine")drawNode(isoX(0.5,0.5),isoY(0.5,0.5),{kind:N.ORE,scale:1.1,variant:0,seed:2,growth:1,amount:5,hidden:false,marked:false},0.3);
      else if(key==="gather")drawNode(isoX(0.5,0.5),isoY(0.5,0.5),{kind:N.BUSH,scale:1.2,variant:0,seed:3,growth:1,amount:3,hidden:false,marked:false},0.3);
      else {
        g.strokeStyle=key==="demo"?"#f0685a":"#8b98ad";g.lineWidth=4;g.lineCap="round";
        if(key==="demo"){g.beginPath();g.moveTo(isoX(0.5,0.5)-13,isoY(0.5,0.5)-24);g.lineTo(isoX(0.5,0.5)+13,isoY(0.5,0.5)+2);
          g.moveTo(isoX(0.5,0.5)+13,isoY(0.5,0.5)-24);g.lineTo(isoX(0.5,0.5)-13,isoY(0.5,0.5)+2);g.stroke();}
        else {g.beginPath();g.arc(isoX(0.5,0.5),isoY(0.5,0.5)-12,12,0,TAU);g.stroke();
          g.beginPath();g.moveTo(isoX(0.5,0.5)-6,isoY(0.5,0.5)-12);g.lineTo(isoX(0.5,0.5)+6,isoY(0.5,0.5)-12);g.stroke();}
      }
    }
  }catch(err){}
  g.restore();
  ctx=real;AMB=ra;WARM=rw;NIGHT=rn;NOFX=rf;
}

/* ── right panel ──────────────────────────────────────────────────────── */
let rpTab="col";
function setRP(t){rpTab=t;$$(".rptab").forEach(b=>b.classList.toggle("on",b.dataset.rp===t));renderRight();}
function cycleRP(){const o=["col","obj","insp","stat"];setRP(o[(o.indexOf(rpTab)+1)%4]);}
$$(".rptab").forEach(b=>b.onclick=()=>{setRP(b.dataset.rp);Audio_.ui();});

const _avCache=new Map();
function avatarFor(c){
  let cvs=_avCache.get(c.id);
  if(!cvs){cvs=document.createElement("canvas");cvs.width=68;cvs.height=68;_avCache.set(c.id,cvs);}
  const g=cvs.getContext("2d");
  g.setTransform(1,0,0,1,0,0);g.clearRect(0,0,68,68);
  const real=ctx,ra=AMB,rw=WARM,rn=NIGHT;
  ctx=g;AMB=1.15;WARM=0.05;NIGHT=0;
  g.fillStyle="#1a2130";g.fillRect(0,0,68,68);
  const gr=g.createRadialGradient(34,20,4,34,40,44);
  gr.addColorStop(0,"rgba(255,255,255,.10)");gr.addColorStop(1,"rgba(0,0,0,.30)");
  g.fillStyle=gr;g.fillRect(0,0,68,68);
  g.translate(34,58);g.scale(1.9,1.9);
  drawHumanoid(0,0,{skin:c.skin,hair:c.hair,shirt:c.cloth,walk:0,moving:false,act:"idle",flip:false,
    scale:c.age<16?0.8:1,hairStyle:c.hairStyle,carry:null,tool:c.tool},0);
  ctx=real;AMB=ra;WARM=rw;NIGHT=rn;
  return cvs;
}
function barHtml(v,col){return '<div class="bar"><i style="width:'+clamp(v,0,100)+'%;background:'+col+'"></i></div>';}
function moodInfo(m){
  if(m>=82)return["Radiante","#5fd69b"];
  if(m>=62)return["Contente","#9fd66a"];
  if(m>=42)return["Neutro","#e0c15c"];
  if(m>=24)return["Infeliz","#ef9a5a"];
  return["Miserável","#f0685a"];
}
function renderRight(){
  const body=$("#rpbody");if(!body)return;
  if(rpTab==="col"){
    const cols=aliveCols().slice().sort((a,b)=>a.id-b.id);
    if(!cols.length){body.innerHTML='<p style="color:var(--muted);font-size:12px">Nenhum colono. A colônia pereceu.</p>';return;}
    body.innerHTML='<div class="sect">Colonos · '+cols.length+"/"+G.housingCap+' abrigos</div>';
    for(const c of cols){
      const e=el("div","col"+(G.sel&&G.sel.type==="col"&&G.sel.id===c.id?" sel":""));
      const [mt,mc]=moodInfo(c.mood);
      const av=avatarFor(c);
      e.innerHTML='<div class="av"></div><div class="info"><div class="row1"><b></b><span>'+(c.militia?"⚔ ":"")+c.age+"a</span></div>"+
        '<div class="act"></div><div class="bars">'+
        barHtml(c.hunger,"#e0a145")+barHtml(c.energy,"#63a9ef")+barHtml(c.health,"#5fd69b")+
        '<div class="bar"><i style="width:'+clamp(c.mood,0,100)+'%;background:'+mc+'"></i></div></div></div>';
      e.querySelector("b").textContent=c.first;
      e.querySelector(".act").textContent=c.stateTxt+(c.job?" · "+Math.round((c.job.prog||0)*100)+"%":"");
      e.querySelector(".av").appendChild(av.cloneNode?av:av);
      e.onclick=()=>{G.sel={type:"col",id:c.id};centerOn(c.x,c.y);renderRight();renderSelBar();Audio_.ui();};
      e.addEventListener("mouseenter",ev=>{
        tipShow("<b>"+c.name+'</b><p>'+c.age+" anos · "+c.traits.map(t=>TRAIT.find(x=>x.id===t).name).join(", ")+"</p>"+
          '<div class="tkv"><span>Humor</span><b style="color:'+mc+'">'+mt+" "+round(c.mood)+"%</b></div>"+
          '<div class="tkv"><span>Fome</span><b>'+round(c.hunger)+"%</b></div>"+
          '<div class="tkv"><span>Energia</span><b>'+round(c.energy)+"%</b></div>"+
          '<div class="tkv"><span>Saúde</span><b>'+round(c.health)+"%</b></div>"+
          '<div class="tkv"><span>Abrigo</span><b>'+(c.home?(c.home.def==="camp"?"Acampamento":"Casa"):"Ao relento")+"</b></div>"+
          '<div class="tkv"><span>Ferramenta</span><b>'+(c.tool?"sim":"não")+"</b></div>"+
          '<div class="tkv"><span>Agasalho</span><b>'+(c.clothes?"sim":"não")+"</b></div>",ev);
      });
      e.addEventListener("mouseleave",tipHide);
      body.appendChild(e);
    }
  } else if(rpTab==="obj"){
    renderObjectives(body);
  } else if(rpTab==="insp"){
    renderInspector(body);
  } else {
    renderStats(body);
  }
}
function modeGoal(){
  const w=MD().win; if(!w)return null;
  if(w.coin)return {t:"Fortuna no cofre",cur:min(w.coin,round(G.stock.coin)),need:w.coin};
  if(w.day)return {t:"Dias de vale resistido",cur:min(w.day,G.t.day),need:w.day};
  return null;
}
let _objSig="";
function renderObjectives(body){
  const m=MD(), p=contractProgress();
  const sig=[G.t.day,G.prestige,G.obj.chain,G.obj.done,G.obj.failed,
             Object.keys(G.unlocked).filter(k=>G.unlocked[k]).join(","),
             p?p.cur+"/"+p.need+"/"+p.left+"/"+p.a.id:"none",fmt(G.stock.coin),G.over?"1":"0"].join("|");
  if(sig===_objSig)return;
  _objSig=sig;
  let html='<div class="sect">'+m.name+' <span style="text-transform:none;letter-spacing:0;font-weight:400">· '+m.kick+'</span></div>'+
    '<p style="font-size:11px;line-height:1.55;color:var(--muted);margin:0 0 4px">'+m.desc+'</p>';

  if(p){
    html+='<div class="sect">Pedido em aberto</div><div class="objcard'+(p.left<=3?" due":"")+'">'+
      '<div class="objh"><b>'+p.c.title+'</b><span>'+(p.left>0?p.left+" d":"vencido")+'</span></div>'+
      '<div class="objfrom">'+p.c.from+
        (m.policy==="chain"?" · ordem "+min(G.obj.chain+1,CAMPAIGN.length)+" de "+CAMPAIGN.length:" · prazo no dia "+p.a.due)+'</div>'+
      '<div class="objbrief">'+p.c.brief+'</div>'+
      barHtml(round(p.pct*100),p.left<=3?"#f0685a":"#f2b45c")+
      '<div class="objrow"><span>'+p.cur+' / '+p.need+'</span><span class="rw">+'+rewardText(p.c.reward||{})+'</span></div>'+
    '</div>';
  } else {
    const wait=m.policy==="chain"
      ?(G.obj.chain>=CAMPAIGN.length?"Todas as ordens do senhor foram cumpridas.":"A próxima ordem chega em "+max(0,G.obj.cooldown)+" dia(s).")
      :(G.obj.cooldown>0?"Ninguém bateu à porta ainda. Mensageiros aparecem a cada poucos dias.":"Nenhum pedido por agora.");
    html+='<div class="sect">Pedido em aberto</div><div class="objwait">'+wait+'</div>';
  }

  if(m.policy==="chain"){
    html+='<div class="sect">Carta do senhor</div><div class="his">';
    for(const id of CAMPAIGN){
      const h=G.obj.history.find(x=>x.id===id);
      html+='<i class="'+(h?(h.ok?"ok":"no"):"")+'">'+(h?(h.ok?"✓ ":"✗ "):"")+(CAMPAIGN.indexOf(id)+1)+' · '+(CONTRACTS[id]?CONTRACTS[id].title:id)+'</i>';
    }
    html+='</div>';
  }
  const g=modeGoal();
  if(g){
    html+='<div class="sect">Meta do modo</div><div class="objcard">'+
      '<div class="objh"><b>'+g.t+'</b><span>'+fmt(g.cur)+' / '+fmt(g.need)+'</span></div>'+
      barHtml(round(clamp(g.cur/g.need,0,1)*100),"#63a9ef")+
      '<div class="objrow"><span>'+(m.win.coin?"moedas guardadas no cofre":"dias vividos no vale")+'</span><span class="rw">encerra a partida</span></div></div>';
  }

  html+='<div class="sect">Prestígio · '+G.prestige+'</div>'+
    '<p style="font-size:10.5px;color:var(--dim);line-height:1.5;margin:0 0 6px">Ganho ao cumprir contratos e erguer monumentos. '+
    'Gasto para liberar técnicas novas na aba <b>Prestígio</b> da construção.</p>';
  const lock=lockedDefs();
  for(const k of lock){
    const d=BDEF[k], can=G.prestige>=d.pres;
    html+='<div class="unl"><div class="ui-ico"><canvas width="58" height="50"></canvas></div><div class="um"><b>'+d.name+'</b>'+
      '<p>'+d.desc+'</p></div>'+
      '<button class="ubtn" data-unl="'+k+'"'+(can?"":" disabled")+'>✦ '+d.pres+'</button></div>';
  }
  const got=Object.keys(G.unlocked).filter(k=>G.unlocked[k]&&BDEF[k]);
  if(lock.length){
    if(got.length)html+='<div class="his" style="margin-top:6px">'+got.map(k=>'<i class="ok">'+BDEF[k].name+'</i>').join("")+'</div>';
  } else {
    html+='<div class="objwait">'+(got.length?"Todas as técnicas da região já são suas.":"O prestígio chega quando o senhor notar o trabalho — contratos e monumentos pagam bem.")+'</div>';
  }

  if(G.obj.history.length){
    html+='<div class="sect">Arquivo · '+G.obj.done+' cumpridos, '+G.obj.failed+' perdidos</div><div class="his">'+
      G.obj.history.slice(-8).map(h=>{
        const c=CONTRACTS[h.id];
        return '<i class="'+(h.ok?"ok":"no")+'">'+(h.ok?"✓":"✗")+' '+(c?c.title:String(h.id))+' · dia '+h.day+'</i>';
      }).join("")+'</div>';
  }
  body.innerHTML=html;
  $$("#rpbody .unl canvas").forEach((cvs,i)=>{
    const k=lock[i]; if(k)renderIcon(cvs,"bld",k);
  });
  $$("#rpbody [data-unl]").forEach(b=>{
    b.onclick=()=>{const k=b.dataset.unl; Audio_.ui(); if(unlockBuilding(k))renderRight();};
  });
}
/* the side panel is hidden on narrow windows — the objectives then open as a modal */
function openObjectives(){
  const rp=$("#rightpanel");
  if(rp&&rp.offsetParent!==null){setRP("obj");return;}
  const holder=document.createElement("div");
  renderObjectives(holder);
  const html=holder.innerHTML;
  _objSig="";
  openModal({title:"Objetivos",sub:MD().name+" · dia "+G.t.day+" · ✦ "+G.prestige,body:html,
    foot:[{label:"Fechar",cls:"pri",fn:closeModal}]});
  $$("#mBody .unl canvas").forEach((cvs,i)=>{
    const k=lockedDefs()[i]; if(k)renderIcon(cvs,"bld",k);
  });
  $$("#mBody [data-unl]").forEach(b=>{
    b.onclick=()=>{const k=b.dataset.unl; Audio_.ui(); if(unlockBuilding(k)){closeModal();openObjectives();}};
  });
}
function renderInspector(body){
  const s=G.sel;
  if(!s||s.type==="tile"){
    if(s&&s.type==="tile"&&inb(s.x,s.y)){
      const i=idx(s.x,s.y);
      body.innerHTML='<div class="sect">Terreno</div>'+
        '<div class="stat"><span>Bioma</span><b>'+BNAME[G.bio[i]]+'</b></div>'+
        '<div class="stat"><span>Fertilidade</span><b>'+G.fer[i]+'%</b></div>'+
        '<div class="stat"><span>Umidade</span><b>'+round(G.moi[i]/255*100)+'%</b></div>'+
        '<div class="stat"><span>Elevação</span><b>'+G.hgt[i]+'/5</b></div>'+
        '<div class="stat"><span>Custo de passagem</span><b>'+(G.cost[i]>=90?"intransitável":G.cost[i].toFixed(2))+'</b></div>'+
        (G.ovr[i]===O.ROAD?'<div class="stat"><span>Sobrepiso</span><b>Estrada</b></div>':"");
      return;
    }
    body.innerHTML='<p style="color:var(--muted);font-size:12px">Clique em algo no mapa para inspecionar.<br><br>'+
      'Dica: selecione um colono para ver suas habilidades, ou uma fazenda para trocar a cultura.</p>';
    return;
  }
  if(s.type==="col"){
    const c=G.cols[s.id];
    if(!c||!c.alive){body.innerHTML="<p style='color:var(--muted)'>—</p>";return;}
    const [mt,mc]=moodInfo(c.mood);
    body.innerHTML='<div class="sect">'+c.name+'</div>'+
      '<div class="stat"><span>Idade</span><b>'+c.age+' anos</b></div>'+
      '<div class="stat"><span>Estado</span><b>'+c.stateTxt+'</b></div>'+
      '<div class="stat"><span>Humor</span><b style="color:'+mc+'">'+mt+' · '+round(c.mood)+'</b></div>'+
      '<div class="stat"><span>Saúde</span><b>'+round(c.health)+'%</b></div>'+
      '<div class="stat"><span>Abrigo</span><b>'+(c.home?(c.home.def==="camp"?"Acampamento":"Casa (q"+c.home.quality+")"):"Ao relento")+'</b></div>'+
      '<div class="stat"><span>Equipamento</span><b>'+(c.tool?"ferramenta":"—")+(c.clothes?", agasalho":"")+'</b></div>'+
      '<div class="sect">Traços</div>'+
      c.traits.map(t=>{const T=TRAIT.find(x=>x.id===t);return '<div class="stat"><span style="color:'+T.col+'">'+T.name+'</span><b style="font-family:var(--ui);font-size:10.5px;color:var(--muted);text-align:right;max-width:150px">'+T.desc+'</b></div>';}).join("")+
      '<div class="sect">Habilidades</div>'+
      SKILLS.filter(k=>c.xp[k]>0||k==="farming"||k==="construction"||k==="forestry").map(k=>
        '<div class="skillrow"><div class="sn">'+SKNAME[k]+'</div><div class="sb"><i style="width:'+
        clamp((Math.sqrt(c.xp[k])/Math.sqrt(2000))*100,0,100)+'%"></i></div><div class="lv">'+c.skill[k]+'</div></div>').join("")+
      '<div class="sect">Registro</div>'+
      '<div class="stat"><span>Construções</span><b>'+c.built+'</b></div>'+
      '<div class="stat"><span>Colheitas</span><b>'+c.harvested+'</b></div>'+
      '<div class="stat"><span>Abates</span><b>'+(c.kills||0)+'</b></div>';
    return;
  }
  if(s.type==="bld"){
    const b=G.buildings[s.id];
    if(!b||b.dead){G.sel=null;renderInspector(body);return;}
    const d=BDEF[b.def];
    let extra="";
    if(b.def==="farm"){
      const cd=CROPS[b.crop];
      extra='<div class="stat"><span>Cultura</span><b>'+cd.name+'</b></div>'+
        '<div class="stat"><span>Estágio</span><b>'+["solo preparado","broto","crescendo","quase pronto","pronto para colher"][b.stage]+'</b></div>'+
        '<div class="stat"><span>Crescimento</span><b>'+round(b.growth*100)+'%</b></div>'+
        '<div class="stat"><span>Fertilidade</span><b>'+G.fer[idx(b.x+1,b.y+1)]+'%</b></div>';
    } else if(b.def==="orchard"){
      extra='<div class="stat"><span>Maturidade</span><b>'+round((b.maturity||0)*100)+'%</b></div>';
    } else if(b.def==="workshop"){
      extra='<div class="sect">Fila de produção</div>'+
        (b.queue.length?b.queue.map((q,i)=>'<div class="stat"><span>'+(i+1)+'. '+RECIPES[q.r].name+'</span><b>'+round(RECIPES[q.r].time)+'s</b></div>').join("")
        :'<p style="color:var(--dim);font-size:11px">Vazia — escolha uma receita na barra abaixo.</p>');
    } else if(b.def==="stock"){
      extra='<div class="stat"><span>Capacidade da colônia</span><b>'+fmt(stockTotal())+' / '+fmt(storageCap())+'</b></div>';
    } else if(b.def==="house"){
      const occ=aliveCols().filter(c=>c.home===b).length;
      extra='<div class="stat"><span>Qualidade</span><b>'+b.quality+'/3</b></div>'+
        '<div class="stat"><span>Camas</span><b>'+(d.beds+b.quality)+'</b></div>'+
        '<div class="stat"><span>Ocupantes</span><b>'+occ+'</b></div>';
    } else if(b.def==="tower"){
      extra='<div class="stat"><span>Milicianos</span><b>'+aliveCols().filter(c=>c.militia).length+' no total</b></div>';
    }
    body.innerHTML='<div class="sect">'+d.name+'</div>'+
      '<div class="stat"><span>Integridade</span><b>'+round(b.hp)+' / '+b.maxhp+'</b></div>'+
      '<div class="stat"><span>Estado</span><b>'+(b.built<1?"Em construção ("+round(b.built*100)+"%)":"Operacional")+'</b></div>'+
      (d.mood?'<div class="stat"><span>Bônus de humor</span><b>+'+d.mood+'</b></div>':"")+
      extra;
    return;
  }
  if(s.type==="node"){
    const n=G.nodes[s.id];
    if(!n||n.dead){G.sel=null;renderInspector(body);return;}
    const d=NODEDEF[n.kind];
    body.innerHTML='<div class="sect">'+d.name+'</div>'+
      '<div class="stat"><span>Rendimento</span><b>'+Object.entries(d.yield).map(([k,v])=>v+" "+(RESDEF.find(r=>r.k===k)||{name:k}).name.toLowerCase()).join(", ")+'</b></div>'+
      '<div class="stat"><span>Trabalho</span><b>'+d.work.toFixed(1)+'s</b></div>'+
      (d.regrow?'<div class="stat"><span>Renovável</span><b>rebrota em '+d.regrow+' dias</b></div>':"")+
      '<div class="stat"><span>Marcado</span><b>'+(n.marked?"sim":"não")+'</b></div>';
    return;
  }
  if(s.type==="enemy"||s.type==="animal"){
    const e=(s.type==="enemy"?G.enemies:G.animals).find(x=>x&&x.id===s.id&&!x.dead);
    if(!e){G.sel=null;renderInspector(body);return;}
    body.innerHTML='<div class="sect">'+e.name+'</div>'+
      '<div class="stat"><span>Vida</span><b>'+round(e.hp)+' / '+e.maxhp+'</b></div>'+
      (e.dmg?'<div class="stat"><span>Dano</span><b>'+e.dmg+'</b></div>':"")+
      '<div class="stat"><span>Estado</span><b>'+(e.flee>0?"fugindo":"caçando")+'</b></div>';
    return;
  }
  if(s.type==="item"){
    const it=G.items.find(i=>i&&i.id===s.id&&!i.dead);
    if(!it){G.sel=null;renderInspector(body);return;}
    const r=RESDEF.find(x=>x.k===it.kind);
    body.innerHTML='<div class="sect">'+r.name+' solta</div>'+
      '<div class="stat"><span>Quantidade</span><b>'+it.amount+'</b></div>'+
      '<div class="stat"><span>Aguardando</span><b>transporte</b></div>';
    return;
  }
}
function renderStats(body){
  const cols=aliveCols();
  const pop=cols.length;
  const daysFood=G.stock.food/max(0.5,pop*0.55);
  const w=wealth();
  body.innerHTML=
    '<div class="sect">Colônia · Ano '+G.year+'</div>'+
    '<div class="stat"><span>Dias sobrevividos</span><b>'+G.t.day+'</b></div>'+
    '<div class="stat"><span>População</span><b>'+pop+' / '+G.housingCap+'</b></div>'+
    '<div class="stat"><span>Humor médio</span><b style="color:'+moodInfo(avgMood())[1]+'">'+round(avgMood())+'%</b></div>'+
    '<div class="stat"><span>Saúde média</span><b>'+round(avgHealth())+'%</b></div>'+
    '<div class="stat"><span>Milicianos</span><b>'+cols.filter(c=>c.militia).length+'</b></div>'+
    '<div class="sect">Economia</div>'+
    '<div class="stat"><span>Riqueza</span><b>'+fmt(w)+'</b></div>'+
    '<div class="stat"><span>Moedas</span><b>'+fmt(G.stock.coin)+'</b></div>'+
    '<div class="stat"><span>Estoque / capacidade</span><b>'+fmt(stockTotal())+' / '+fmt(storageCap())+'</b></div>'+
    '<div class="stat"><span>Comida para</span><b style="color:'+(daysFood<3?"#f0685a":daysFood<7?"#e0c15c":"#5fd69b")+'">'+daysFood.toFixed(1)+' dias</b></div>'+
    '<div class="stat"><span>Ameaça</span><b style="color:'+(G.threat>40?"#f0685a":"#8b98ad")+'">'+round(G.threat)+'/100</b></div>'+
    '<div class="stat"><span>Caravana</span><b>'+(G.market.here?"no vale":"em "+max(0,G.market.next-G.t.day)+" dias")+'</b></div>'+
    '<div class="sect">Preços dos mercadores</div>'+
    RESDEF.filter(r=>r.k!=="coin").map(r=>{
      const p=G.prices[r.k];if(!p)return "";
      const diff=(p.buy/r.base-1);
      return '<div class="stat"><span style="color:'+r.col+'">'+r.name+'</span><b class="'+(diff>0.06?"dn":diff<-0.06?"up":"")+'">'+
        p.buy.toFixed(1)+' <span style="color:var(--dim)">'+(diff>0?"▲":diff<0?"▼":"■")+'</span></b></div>';
    }).join("")+
    '<div class="sect">Registro</div>'+
    '<div class="stat"><span>Construções</span><b>'+G.stats.built+'</b></div>'+
    '<div class="stat"><span>Árvores cortadas</span><b>'+G.stats.chopped+'</b></div>'+
    '<div class="stat"><span>Colheitas</span><b>'+G.stats.harvested+'</b></div>'+
    '<div class="stat"><span>Invasões</span><b>'+G.stats.waves+'</b></div>'+
    '<div class="stat"><span>Mortes</span><b>'+G.stats.died+'</b></div>'+
    '<div class="sect">Semente</div>'+
    '<div class="stat"><span>Mundo</span><b style="font-size:10px">'+String(G.seed).slice(0,14)+'</b></div>';
}

/* ── contextual action bar ────────────────────────────────────────────── */
function renderSelBar(){
  const bar=$("#selbar");
  const s=G.sel;
  let html="";
  if(G.tool){
    html+='<button class="sbtn danger" data-a="cancel">Cancelar ferramenta (Esc)</button>';
  } else if(s&&s.type==="bld"){
    const b=G.buildings[s.id];
    if(b&&!b.dead){
      if(b.def==="farm"){
        html+='<span style="font-size:11px;color:var(--muted)">Cultura:</span>';
        for(const k of CROPORDER){
          html+='<button class="sbtn'+(b.crop===k?" on":"")+'" data-a="crop" data-v="'+k+'">'+CROPS[k].name+'</button>';
        }
      }
      if(b.def==="workshop"&&b.built>=1){
        html+='<span style="font-size:11px;color:var(--muted)">Fabricar:</span>';
        for(const k of RECIPEORDER){
          const ok=canAfford(RECIPES[k].in);
          html+='<button class="sbtn" data-a="recipe" data-v="'+k+'" '+(ok?"":"disabled")+'>'+RECIPES[k].name+'</button>';
        }
      }
      if(b.def==="tower"){
        html+='<span style="font-size:11px;color:var(--muted)">Milícia:</span>';
        html+='<button class="sbtn" data-a="militia">Recrutar/dispensar</button>';
      }
      html+='<button class="sbtn danger" data-a="demo">Demolir</button>';
    }
  } else if(s&&s.type==="col"){
    const c=G.cols[s.id];
    if(c&&c.alive){
      html+='<button class="sbtn'+(c.militia?" on":"")+'" data-a="mil">Milícia</button>';
      html+='<button class="sbtn" data-a="follow">Centralizar</button>';
      if(c.job)html+='<button class="sbtn danger" data-a="release">Dispensar tarefa</button>';
    }
  } else if(s&&s.type==="node"){
    const n=G.nodes[s.id];
    if(n&&!n.dead){
      const k=n.kind;
      if(k<=3||k===8)html+='<button class="sbtn" data-a="mark" data-v="chop">Cortar</button>';
      else if(k===5||k===6)html+='<button class="sbtn" data-a="mark" data-v="mine">Minerar</button>';
      else html+='<button class="sbtn" data-a="mark" data-v="gather">Coletar</button>';
      html+='<button class="sbtn danger" data-a="demoNode">Remover</button>';
    }
  } else if(G.market.here){
    html+='<button class="sbtn" data-a="trade">Falar com a caravana</button>';
  }
  bar.innerHTML=html;
  bar.classList.toggle("on",!!html);
  bar.querySelectorAll(".sbtn").forEach(b=>{
    b.onclick=()=>{
      const a=b.dataset.a,v=b.dataset.v;
      Audio_.ui();
      if(a==="cancel")setTool(null);
      else if(a==="crop"){const bb=G.buildings[G.sel.id];if(bb){bb.crop=v;bb.stage=0;bb.growth=0;bb.tilled=bb.tilled;renderSelBar();renderRight();}}
      else if(a==="recipe"){const bb=G.buildings[G.sel.id];
        if(bb){if(bb.queue.length>8){hint("Fila cheia (máx. 9)");return;}
          if(!canAfford(RECIPES[v].in)){hint("<b>Recursos insuficientes</b>");Audio_.err();return;}
          bb.queue.push({r:v});hint("Na fila: "+RECIPES[v].name);renderRight();}}
      else if(a==="militia"){setRP("col");hint("Use o botão <b>Milícia</b> ao selecionar um colono.");}
      else if(a==="demo"){const bb=G.buildings[G.sel.id];if(bb){addJob({type:"clear",x:bb.x,y:bb.y,bx:bb.id,prio:6,work:2});hint("Demolição marcada");}}
      else if(a==="demoNode"){const n=G.nodes[G.sel.id];if(n){addJob({type:"clear",x:n.x,y:n.y,node:n.id,prio:6,work:1.4});hint("Remoção marcada");}}
      else if(a==="mark"){const n=G.nodes[G.sel.id];if(n)markNode(n,v);}
      else if(a==="mil"){const c=G.cols[G.sel.id];if(c){c.militia=!c.militia;
        notify(c.militia?"Recrutado":"Dispensado",c.first+(c.militia?" agora defende a colônia.":" voltou ao trabalho civil."),"info");
        renderSelBar();renderRight();}}
      else if(a==="follow"){const c=G.cols[G.sel.id];if(c)centerOn(c.x,c.y);}
      else if(a==="release"){const c=G.cols[G.sel.id];if(c)releaseJob(c);}
      else if(a==="trade")openTrade();
    };
  });
}

/* ── modals ───────────────────────────────────────────────────────────── */
let _modalDismissable=true;
function openModal(o){
  $("#mTitle").textContent=o.title;
  $("#mSub").textContent=o.sub||"";
  $("#mBody").innerHTML=o.body||"";
  const f=$("#mFoot");f.innerHTML="";
  for(const b of (o.foot||[])){
    const btn=el("button","btn "+(b.cls||""),b.label);
    btn.onclick=()=>{Audio_.ui();b.fn&&b.fn();};
    f.appendChild(btn);
  }
  _modalDismissable=o.dismissable!==false;
  $("#modalwrap").classList.add("on");
  if(o.onOpen)o.onOpen();
}
function closeModal(){$("#modalwrap").classList.remove("on");}
$("#mClose").onclick=()=>{if(_modalDismissable)closeModal();};
$("#modalwrap").addEventListener("click",e=>{if(e.target.id==="modalwrap"&&_modalDismissable)closeModal();});

function openTrade(){
  if(!G.market.here){hint("Nenhuma caravana no vale agora.");Audio_.err();return;}
  const body='<p style="color:var(--muted);font-size:12px;margin-bottom:10px">Os mercadores ficam '+G.market.leave+' dia(s). Preços mudam conforme a oferta — vender muito derruba o preço.</p>'+
    RESDEF.filter(r=>r.k!=="coin").map(r=>{
      const p=G.prices[r.k];
      const diff=p.buy/r.base-1;
      const arrow=diff>0.06?'<span class="ar dn">▲</span>':diff<-0.06?'<span class="ar up">▼</span>':'<span class="ar" style="color:var(--dim)">■</span>';
      const stock=Math.round(G.market.goods.find(g=>g.k===r.k)?.qty||0);
      return '<div class="traderow" data-k="'+r.k+'">'+
        '<div class="tn"><div class="sw" style="--c:'+r.col+'"></div>'+r.name+
          '<span style="color:var(--dim);font-size:10.5px;font-weight:400">tem '+fmt(G.stock[r.k])+(stock?" · caravana "+stock:"")+'</span></div>'+
        '<div class="trend">'+arrow+'<span style="color:var(--text)">'+p.buy.toFixed(1)+'</span></div>'+
        '<div class="trend" style="color:var(--muted)">vende <span style="color:var(--green)">'+p.sell.toFixed(1)+'</span></div>'+
        '<div style="display:flex;gap:5px">'+
          '<div class="qbox"><button data-a="-">−</button><input value="5" data-q><button data-a="+">+</button></div>'+
          '<button class="btn" data-buy style="padding:5px 9px;font-size:11px">Comprar</button>'+
          '<button class="btn" data-sell style="padding:5px 9px;font-size:11px">Vender</button>'+
        '</div></div>';
    }).join("")+
    '<div class="traderow" style="border-top:1px solid var(--line);margin-top:6px;padding-top:12px"><div class="tn"><div class="sw" style="--c:#e0a145"></div>Moedas</div><div></div><div></div><div class="trend" style="justify-content:flex-end;color:var(--gold)"><b id="coinTot" style="font-size:15px">'+fmt(G.stock.coin)+'</b></div></div>';
  openModal({
    title:"Caravana de mercadores",sub:"Compre o que falta, venda o que sobra",
    body,
    foot:[{label:"Fechar",cls:"pri",fn:closeModal}],
    onOpen(){
      $("#mBody").querySelectorAll(".traderow[data-k]").forEach(row=>{
        const k=row.dataset.k;
        const inp=row.querySelector("[data-q]");
        row.querySelectorAll(".qbox button").forEach(b=>b.onclick=()=>{
          inp.value=clamp((parseInt(inp.value)||0)+(b.dataset.a==="+"?5:-5),1,999);Audio_.ui();
        });
        row.querySelector("[data-buy]").onclick=()=>{
          const q=parseInt(inp.value)||0;
          const avail=Math.round(G.market.goods.find(g=>g.k===k)?.qty||0);
          const n=min(q,avail);
          if(n<=0){hint("A caravana não tem mais disso.");Audio_.err();return;}
          const cost=Math.round(n*G.prices[k].buy*priceMult());
          if(G.stock.coin<cost){hint("Moedas insuficientes ("+cost+" necessárias).");Audio_.err();return;}
          if(stockTotal()+n>storageCap()){hint("Armazéns cheios.");Audio_.err();return;}
          G.stock.coin-=cost;addStock(k,n);
          const g=G.market.goods.find(x=>x.k===k);g.qty-=n;
          G.prices[k].buy*=1+0.014*n;G.prices[k].mom+=0.02*n;
          Audio_.coin();refreshTrade();
          notify("Compra",n+"× "+RESDEF.find(r=>r.k===k).name+" por "+cost+" moedas.","info");
        };
        row.querySelector("[data-sell]").onclick=()=>{
          const q=min(parseInt(inp.value)||0,G.stock[k]|0);
          if(q<=0){hint("Você não tem "+RESDEF.find(r=>r.k===k).name.toLowerCase()+".");Audio_.err();return;}
          const gain=Math.round(q*G.prices[k].sell);
          G.stock[k]-=q;G.stock.coin+=gain;G.stats.traded+=gain;
          G.prices[k].buy*=max(0.72,1-0.011*q);G.prices[k].mom-=0.02*q;
          Audio_.coin();refreshTrade();
          notify("Venda",q+"× "+RESDEF.find(r=>r.k===k).name+" por "+gain+" moedas.","good");
        };
      });
    }
  });
}
function refreshTrade(){
  $("#coinTot").textContent=fmt(G.stock.coin);
  $("#mBody").querySelectorAll(".traderow[data-k]").forEach(row=>{
    const k=row.dataset.k,p=G.prices[k];
    const diff=p.buy/RESDEF.find(r=>r.k===k).base-1;
    const ar=row.querySelector(".ar");
    ar.className="ar "+(diff>0.06?"dn":diff<-0.06?"up":"");
    ar.textContent=diff>0.06?"▲":diff<-0.06?"▼":"■";
    const tds=row.querySelectorAll(".trend span");
    if(tds[1])tds[1].textContent=p.buy.toFixed(1);
    if(tds[2])tds[2].textContent=p.sell.toFixed(1);
    const info=row.querySelector(".tn span");
    const stock=Math.round(G.market.goods.find(g=>g.k===k)?.qty||0);
    info.textContent="tem "+fmt(G.stock[k])+(stock?" · caravana "+stock:"");
  });
}
function openHelp(){
  openModal({
    title:"Como governar o vale",sub:"Guia rápido e atalhos",
    body:'<div class="helpgrid"><div class="helpsec">'+
      '<h4>Primeiros passos</h4>'+
      '<p>1. Use <b>Cortar árvores</b> e arraste sobre a floresta — os colonos derrubam e deixam a madeira no chão.</p>'+
      '<p>2. Construa um <b>Depósito</b>: sem ele, os colonos só carregam até o ponto de descarga do acampamento (capacidade baixa).</p>'+
      '<p>3. Marque <b>Minerar rochas</b> para obter pedra, então erga uma <b>Casa</b> antes da noite.</p>'+
      '<p>4. Prepare uma <b>Fazenda</b> na primavera (solo com fertilidade ≥ 22). Ela é arada, semeada e colhida sozinha.</p>'+
      '<h4>Sobrevivência</h4>'+
      '<p>Cada colono tem <b>fome, energia, humor e saúde</b>. Sem comida, adoecem. Sem casa no inverno, congelam. Humor baixo causa crises nervosas.</p>'+
      '<p><b>Tecido</b> vira agasalho automaticamente no inverno (2 por colono). <b>Ferramentas</b> dão +30% de velocidade de trabalho.</p>'+
      '<p>A <b>ameaça</b> cresce com a sua riqueza: construa <b>Muros</b> e <b>Torres</b>, e recrute <b>Milícia</b> selecionando um colono.</p>'+
      '</div><div class="helpsec">'+
      '<h4>Modos de jogo</h4>'+
      '<p><b style="color:#7ec87e">Colônia Livre</b> — sandbox: sem prazos, sem fim. Pedidos pontuais rendem prestígio.</p>'+
      '<p><b style="color:#f2b45c">Carta do Senhor</b> — seis ordens feudais em cadeia, cada uma com prazo. Cumprir todas encerra a campanha.</p>'+
      '<p><b style="color:#f0685a">Vale Implacável</b> — estoque mínimo, frio que mata, invasões em dobro, sem imigrantes e sem autosave. Sobreviva três invernos.</p>'+
      '<p><b style="color:#63a9ef">Rota das Caravanas</b> — paz permanente e mercado volátil: acumule 1.200 moedas.</p>'+
      '<h4>Contratos e prestígio</h4>'+
      '<p>Cada pedido mostra <b>progresso, prazo e recompensa</b> na faixa abaixo do relógio e no painel <b>Objetivos</b> (tecla <b>O</b>).</p>'+
      '<p>Prestígio (✦) vem de contratos cumpridos e monumentos. Gastando-o você libera moinho, forno, celeiro, escola e quartel na aba <b>Prestígio</b> da construção.</p>'+
      '<p>Moinho produz <b>farinha</b>; o forno transforma farinha em <b>pão</b> — comida melhor, mais humor e mais resistência ao frio.</p>'+
      '</div><div class="helpsec"><h4>Atalhos</h4><div class="keys">'+
      [["Espaço","pausar / retomar"],[",  /  .","velocidade −/+"],["Esc","cancelar ferramenta"],["H","esta ajuda"],["M","ligar/desligar som"],["Tab","trocar painel"],["O","objetivos e prestígio"],["1…5","ordens (cortar, minerar, coletar, demolir, cancelar)"],["Q E R T","estrada, depósito, casa, poço"],["F G V B","fazenda, pomar, oficina, mina"],["N I","mercado, enfermaria"],["Z X","muro, torre"],["C L K","fogueira, lampião, monumento"],["J P D","moinho, forno, celeiro (após liberar)"],["A U","escola, quartel (após liberar)"],["Botão direito","cancelar / desmarcar"],["Arrastar com o botão do meio","mover a câmera"],["Roda do mouse","zoom"],["WASD / setas","mover a câmera"],["Ctrl + clique","colocar uma vez só"]]
      .map(k=>'<div class="keyrow"><span>'+k[1]+'</span><kbd>'+k[0]+'</kbd></div>').join("")+
      '</div><h4 style="margin-top:14px">Estações</h4>'+
      SEASONS.map(s=>'<div class="keyrow"><span style="color:'+s.col+'">'+s.name+' — '+s.desc+'</span><b style="font-family:var(--mono);font-size:10.5px">'+SEASON_DAYS+'d</b></div>').join("")+
      '</div></div>',
    foot:[{label:"Entendi",cls:"pri",fn:closeModal}]
  });
}
$("#btnHelp").onclick=()=>{Audio_.init();openHelp();};
$("#btnTrade").onclick=()=>{Audio_.init();openTrade();};
function toggleSound(){
  Audio_.init();Audio_.enabled=!Audio_.enabled;
  if(Audio_.master)Audio_.master.gain.value=Audio_.enabled?0.5:0;
  $("#btnSound").style.opacity=Audio_.enabled?1:0.42;
  $("#sndW1").style.opacity=Audio_.enabled?1:0.15;
  $("#sndW2").style.opacity=Audio_.enabled?1:0.15;
}
$("#btnSound").onclick=toggleSound;
$("#btnMenu").onclick=openMenu;
function openMenu(){
  openModal({
    title:"Menu",sub:"Vale de Auroria",
    body:'<div class="helpsec"><p>Salve seu progresso, reinicie com um novo vale ou reveja o guia.</p></div>'+
      '<div class="stat"><span>Dia</span><b>'+G.t.day+'</b></div>'+
      '<div class="stat"><span>Ano</span><b>'+G.year+'</b></div>'+
      '<div class="stat"><span>População</span><b>'+aliveCols().length+'</b></div>'+
      '<div class="stat"><span>Riqueza</span><b>'+fmt(wealth())+'</b></div>',
    foot:[
      {label:"Guia",fn:openHelp},
      {label:"Salvar",cls:"",fn:()=>{saveGame();notify("Jogo salvo","Progresso guardado neste navegador.","good");}},
      {label:"Novo vale",cls:"dgr",fn:()=>{closeModal();showTitle();}},
      {label:"Voltar ao jogo",cls:"pri",fn:closeModal}
    ]
  });
}

/*═══════════════════════════════════════════════════════════════════════════════
  Part 13 · persistence, bootstrap, main loop
═══════════════════════════════════════════════════════════════════════════════*/

const SAVE_KEY="auroria.vale.v2";
const VALLEY_NAMES=["Auroria","Vale Claro","Rio Prateado","Colina Verde","Pedra Serena",
  "Vau das Garças","Campo Alto","Fonte Fria","Bosque Longo","Terras de Âmbar"];

/* ── typed array ⇄ base64 ─────────────────────────────────────────────── */
function ta2b64(ta){
  const u8=new Uint8Array(ta.buffer,ta.byteOffset,ta.byteLength);
  let s=""; const CH=0x8000;
  for(let i=0;i<u8.length;i+=CH)s+=String.fromCharCode.apply(null,u8.subarray(i,i+CH));
  return btoa(s);
}
function b64ta(str,Ctor){
  const bin=atob(str), u8=new Uint8Array(bin.length);
  for(let i=0;i<bin.length;i++)u8[i]=bin.charCodeAt(i);
  return new Ctor(u8.buffer,0,u8.byteLength/Ctor.BYTES_PER_ELEMENT);
}

function resetRun(mode){
  G.cols.length=0;G.items.length=0;G.jobs.length=0;G.enemies.length=0;
  G.animals.length=0;G.particles.length=0;G.floats.length=0;
  G.stock={wood:0,stone:0,food:0,cloth:0,tools:0,flour:0,bread:0,coin:0};
  G.flow={wood:0,stone:0,food:0,cloth:0,tools:0};
  G.t={min:6*60,day:0,year:1,speed:1,paused:false,elapsed:0};
  G.stats={built:0,chopped:0,harvested:0,traded:0,killed:0,died:0,daysSurvived:0,waves:0,contracts:0};
  G.market={next:4,goods:[],here:false,leave:0};
  G.buff={festival:0};G.prices={};G.militia=[];G.arms=0;
  G.season=0;G.seasonDay=0;G.temp=12;G.wx={type:"clear",t:0,next:2,lightning:0};
  G.sel=null;G.tool=null;G.over=false;G.started=false;G._fireOn=false;G._sealWarn=false;G._storeWarn=false;
  G.threat=0;G.popPeak=0;G.moodShock=0;G.camp=null;G.campBld=null;
  G.mode=(mode&&MODES[mode])?mode:"livre";
  G.prestige=0;G.prestigeEarned=0;G.unlocked={};
  G.obj={active:null,chain:0,done:0,failed:0,cooldown:0,history:[]};
  G._lastSeasonDay=undefined;G._lastDaily=undefined;
  _lastDay=-1;_dailyAcc=0;
  _avCache.clear();
  _objSig="";
  _homeRegion=0;
  invalidateDrop();
}

/* ── save ─────────────────────────────────────────────────────────────── */
function saveGame(){
  if(!G.started||!G.bio)return false;
  try{
    const cols=[];
    for(const c of G.cols){
      if(!c||!c.alive)continue;
      const o=Object.assign({},c);
      o.path=null;o.pi=0;o.moving=false;o.dest=null;o.job=null;o.target=null;o.tower=null;
      o.home=c.home?(c.home.id||-1):0;
      cols.push(o);
    }
    const jobs=[];
    for(const j of G.jobs){if(j&&!j.dead){const o=Object.assign({},j);o.by=0;o.prog=0;jobs.push(o);}}
    const buildings=[];
    for(const b of G.buildings){if(b&&!b.dead){const o=Object.assign({},b);o.militia=[];buildings.push(o);}}
    const strip=o=>{const c=Object.assign({},o);c.path=null;c.pi=0;c.target=null;return c;};
    const data={
      v:2, seed:G.seed, name:G.name, camp:G.camp, mode:G.mode,
      prestige:G.prestige, prestigeEarned:G.prestigeEarned, unlocked:G.unlocked, obj:G.obj,
      maps:{ovr:ta2b64(G.ovr),res:ta2b64(G.res),bld:ta2b64(G.bld),
            block:ta2b64(G.block),fire:ta2b64(G.fire),smoke:ta2b64(G.smoke)},
      ids:{nid:G.nid,bid:G.bid,cid:G.cid,eid:G.eid,aid:G.aid},
      nodes:G.nodes.filter(n=>n&&!n.dead),
      buildings, cols, jobs,
      items:G.items.filter(i=>i&&!i.dead),
      enemies:G.enemies.filter(e=>e&&!e.dead).map(strip),
      animals:G.animals.filter(a=>a&&!a.dead).map(strip),
      stock:G.stock,cap:G.cap,flow:G.flow,t:G.t,
      season:G.season,seasonDay:G.seasonDay,temp:G.temp,wx:G.wx,
      stats:G.stats,prices:G.prices,market:G.market,buff:G.buff,
      threat:G.threat,popPeak:G.popPeak,housingCap:G.housingCap,arms:G.arms,
      flags:{sd:G._lastSeasonDay,dd:G._lastDaily,day:_lastDay,shock:G.moodShock||0}
    };
    localStorage.setItem(SAVE_KEY,JSON.stringify(data));
    return true;
  }catch(err){
    console.warn("save failed",err);
    notify("Não foi possível salvar",String(err&&err.message||err).slice(0,80),"bad");
    return false;
  }
}

/* ── load ─────────────────────────────────────────────────────────────── */
function loadGame(){
  const raw=localStorage.getItem(SAVE_KEY);
  if(!raw)return false;
  let d; try{d=JSON.parse(raw);}catch(e){return false;}
  if(!d||d.v!==2||!d.seed)return false;
  try{
    resetRun(d.mode);
    genWorld(d.seed);
    G.ovr.set(b64ta(d.maps.ovr,Uint8Array));
    G.res.set(b64ta(d.maps.res,Int32Array));
    G.bld.set(b64ta(d.maps.bld,Int32Array));
    G.block.set(b64ta(d.maps.block,Uint8Array));
    G.fire.set(b64ta(d.maps.fire,Float32Array));
    rebuildFireSet();
    G.smoke.set(b64ta(d.maps.smoke,Float32Array));
    G.nodes.length=0; for(const n of d.nodes)G.nodes[n.id]=n;
    G.buildings.length=0; for(const b of d.buildings)G.buildings[b.id]=b;
    G.cols.length=0;
    for(const c of d.cols){
      c.path=null;c.pi=0;c.job=null;c.moving=false;c.dest=null;c.target=null;
      c.state="idle";c.stateTxt="Ocioso";c.phase="";c.workT=0;c.seekT=0;
      G.cols[c.id]=c;
    }
    G.jobs.length=0; for(const j of d.jobs)G.jobs.push(j);
    G.items=d.items.slice(); G.enemies=d.enemies.slice(); G.animals=d.animals.slice();
    G.name=d.name||"Colônia";G.camp=d.camp||findCamp();
    makeCampBld();
    for(const c of G.cols){
      if(!c)continue;
      c.home=typeof c.home==="number"?(c.home===-1?G.campBld:(c.home?(G.buildings[c.home]||null):null)):null;
      c.bed=c.bed||0;
    }
    G.nid=d.ids.nid;G.bid=d.ids.bid;G.cid=d.ids.cid;G.eid=d.ids.eid;G.aid=d.ids.aid;
    G.stock=Object.assign(G.stock,d.stock||{});
    G.cap=d.cap||G.cap;G.flow=Object.assign(G.flow,d.flow||{});
    G.t=d.t;G.season=d.season;G.seasonDay=d.seasonDay;G.temp=d.temp;G.wx=d.wx;
    G.stats=Object.assign(G.stats,d.stats||{});G.prices=d.prices;G.market=d.market;G.buff=d.buff;
    G.threat=d.threat;G.popPeak=d.popPeak;G.arms=d.arms||0;
    G.prestige=d.prestige||0;G.unlocked=d.unlocked||{};
    G.obj=Object.assign({active:null,chain:0,done:0,failed:0,cooldown:0,history:[]},d.obj||{});
    G._lastSeasonDay=d.flags.sd;G._lastDaily=d.flags.dd;
    _lastDay=d.flags.day;G.moodShock=d.flags.shock||0;
    G.rng=new RNG((d.seed^0x51ed7a3)>>>0);
    recomputeCost();
    rebuildRegions();
    initVisual();
    resizeLight();
    invalidateDrop();
    assignHomes();
    setWeather(G.wx.type);
    G.over=false;G.started=true;G.t.paused=false;G.t.speed=clamp(G.t.speed|0||1,1,3);
    G.sel=null;G.tool=null;G.hoverTile=null;
    _avCache.clear();
    buildResBar();syncResBaseline();buildMenu();_menuSig=menuSig();
    renderRight();renderSelBar();syncSpeedUI();updateHUD(0);updateGoalBar();
    G.cam.z=1.1;centerOn(G.camp.x,G.camp.y,true);
    hideTitle();
    _tutOn=false;$("#hint").classList.remove("on");
    banner(G.name.toUpperCase(),"dia "+G.t.day+" · "+SEASONS[G.season].name+" do ano "+G.year);
    notify("Partida carregada","Bem-vindo de volta ao vale — modo "+MD().name+".","good");
    Audio_.init();Audio_.bell();
    return true;
  }catch(err){
    console.warn("load failed",err);
    notify("Save corrompido","Não foi possível restaurar a partida.","bad");
    return false;
  }
}
function hasSave(){try{return !!localStorage.getItem(SAVE_KEY);}catch(e){return false;}}
let _autoT=14;
function autosave(){
  if(!G.started||G.over)return;
  if(!MD().autosave)return;          // implacável: só se salva quando se quer
  if(saveGame()){$("#btnContinue").disabled=false;}
}

/* ── title screen ─────────────────────────────────────────────────────── */
function hideTitle(){$("#title").classList.add("out");}

/* ── mode picker ──────────────────────────────────────────────────────── */
let _modeSel="livre";
const TICK_SVG='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="3.2" stroke-linecap="round" stroke-linejoin="round"><path d="M5 13l4 4L19 7"/></svg>';
function renderModes(){
  const box=$("#modes"); if(!box)return;
  box.innerHTML="";
  MODEORDER.forEach((key,i)=>{
    const m=MODES[key];
    const c=el("div","modecard"+(key===_modeSel?" on":""),
      '<div class="mnum">'+(i+1)+'</div><div class="mtick">'+TICK_SVG+'</div>'+
      '<div class="mh"><div class="mi">'+(ICONS[m.icon]||ICONS.star)+'</div>'+
      '<div style="min-width:0"><div class="mn">'+m.name+'</div><div class="mk">'+m.kick+'</div></div></div>'+
      '<div class="md">'+m.desc+'</div>'+
      '<div class="ms">'+m.sub+'</div>');
    c.style.setProperty("--mc",m.col);
    c.onclick=()=>{Audio_.init();Audio_.ui();setMode(key);};
    box.appendChild(c);
  });
  setLabel();
}
function setMode(key){
  if(!MODES[key])return;
  _modeSel=key;
  $$("#modes .modecard").forEach((c,i)=>c.classList.toggle("on",MODEORDER[i]===key));
  setLabel();
}
function setLabel(){
  const b=$("#btnNew"); if(!b)return;
  const m=MODES[_modeSel];
  b.textContent=m&&m.policy==="chain"?"Iniciar Campanha":"Nova Colônia";
  b.title=m?m.name+" — "+m.sub:"";
}
function showTitle(){
  closeModal();
  G.started=false;G.t.paused=true;
  setTool(null);G.sel=null;
  $("#hint").classList.remove("on");
  $("#goalbar").classList.remove("on");
  _tutOn=false;
  const t=$("#title");
  t.classList.remove("out");
  // restart the entrance animation
  const inner=t.querySelector(".inner");
  if(inner){inner.style.animation="none";void inner.offsetWidth;inner.style.animation="";}
  const has=hasSave();
  const bc=$("#btnContinue");
  bc.disabled=!has;
  bc.title=has?"Retomar o vale salvo":"Nenhuma partida salva neste navegador";
  const si=$("#seedInput");
  if(!si.value.trim())si.value=randSeedWord();
  renderModes();
}
function randSeedWord(){
  const a=VALLEY_NAMES[(Math.random()*VALLEY_NAMES.length)|0];
  return a.toLowerCase().replace(/[^a-z]/g,"")+"-"+randInt(100,9999);
}

/* ── new game ─────────────────────────────────────────────────────────── */
function startGame(rawSeed,mode){
  let s;
  if(rawSeed===undefined||rawSeed===null||String(rawSeed).trim()===""){s=(Math.random()*1e9)|0;}
  else{
    const t=String(rawSeed).trim();
    s=/^-?\d+$/.test(t)?(parseInt(t,10)|0):(hashStr(t)>>>0);
  }
  resetRun(mode);
  genWorld(s);
  initVisual();
  resizeLight();

  const camp=findCamp();
  G.camp=camp;
  G.name=VALLEY_NAMES[hashStr(String(s))%VALLEY_NAMES.length];
  makeCampBld();

  // clear a small building plot right around the landing spot
  for(let dy=-2;dy<=2;dy++)for(let dx=-2;dx<=2;dx++){
    const x=camp.x+dx,y=camp.y+dy; if(!inb(x,y))continue;
    const n=G.res[idx(x,y)]?G.nodes[G.res[idx(x,y)]]:null;
    if(n&&!n.dead&&NODEDEF[n.kind].hp)delNode(n);
  }

  Object.assign(G.stock,{wood:55,stone:20,food:60,cloth:8,tools:1,coin:35},MD().start||{});
  rebuildRegions();

  const spots=[];
  for(let r=1;r<=4&&spots.length<4;r++)
    for(let dy=-r;dy<=r&&spots.length<4;dy++)
      for(let dx=-r;dx<=r&&spots.length<4;dx++){
        const x=camp.x+dx,y=camp.y+dy;
        if(!inb(x,y)||!passable(idx(x,y)))continue;
        spots.push({x,y});
      }
  while(spots.length<4)spots.push({x:camp.x,y:camp.y});
  spots.forEach((p,k)=>makeColonist(p.x,p.y,k===0));

  // wildlife across the valley
  let tries=0,placed=0;
  while(placed<26&&tries++<6000){
    const x=randInt(6,MAP_W-7),y=randInt(6,MAP_H-7),i=idx(x,y);
    if(!passable(i))continue;
    const b=G.bio[i];
    if(b!==B.MEADOW&&b!==B.FOREST&&b!==B.GRASS)continue;
    if(dist(x,y,camp.x,camp.y)<11)continue;
    spawnAnimal(chance(.32)?"deer":"rabbit",x,y);placed++;
  }

  assignHomes();
  initPrices();
  setWeather("clear");
  G.over=false;G.started=true;G.t.paused=false;G.t.speed=1;
  G.popPeak=aliveCols().length;

  _avCache.clear();
  buildResBar();syncResBaseline();buildMenu();_menuSig=menuSig();
  renderRight();renderSelBar();syncSpeedUI();updateHUD(0);updateGoalBar();
  G.cam.z=1.1;centerOn(camp.x,camp.y,true);
  hideTitle();
  banner(G.name.toUpperCase(),MD().sub||"4 colonos · primavera do ano 1");
  Audio_.init();Audio_.bell();
  startTutorial();
  _autoT=18;
}

/* ── tutorial ─────────────────────────────────────────────────────────── */
const TUT=[
  {html:'Bem-vindo ao vale. <b>WASD</b> move a câmera, a <b>roda do mouse</b> dá zoom e o <b>botão do meio</b> arrasta o mapa.',wait:11},
  {html:'Pressione <b>1</b> (Cortar árvores) e arraste sobre a floresta. Os colonos marcam, derrubam e trazem a lenha sozinhos.',
   wait:20,done:()=>G.stats.chopped>=4},
  {html:'A madeira se acumula no acampamento. Erga um <b>Depósito</b> (tecla <b>E</b>) para ampliar o estoque além de 260.',
   wait:22,done:()=>G.stats.built>=1},
  {html:'Construa <b>Casas</b> (tecla <b>R</b>) cedo: quem dorme ao relento perde calor e humor — e o inverno não perdoa.',
   wait:22,done:()=>G.housingCap>4},
  {html:'Uma <b>Fazenda</b> (tecla <b>F</b>) alimenta a colônia. Selecione-a para arar, escolher a cultura e semear; cada planta tem sua estação.',
   wait:24,done:()=>G.stats.harvested>=1},
  {html:'Quando uma caravana chegar, abra o <b>Comércio</b> no canto superior. Os preços oscilam com a escassez — venda caro, compre barato.',wait:14},
  {html:'Clique num colono para ver desejos, humor e habilidades. <b>Tab</b> alterna os painéis, <b>H</b> abre o guia, <b>Espaço</b> pausa.',wait:14},
  {html:'Cada pedido em aberto aparece na faixa abaixo do relógio. Pressione <b>O</b> para ver prazos, recompensas e o que o seu <b>prestígio</b> já pode liberar.',wait:16},
];
let _tutI=0,_tutT=0,_tutOn=false,_tutShown=false;
function startTutorial(){_tutI=0;_tutT=1.4;_tutOn=true;_tutShown=false;}
function tutorialTick(dt){
  if(!_tutOn)return;
  _tutT-=dt;
  const s=TUT[_tutI];
  if(!s){_tutOn=false;$("#hint").classList.remove("on");return;}
  if(!_tutShown){
    if(_tutT>0)return;
    tutHint(s.html);
    _tutShown=true;_tutT=s.wait||14;
    return;
  }
  if(_tutT<=0||(s.done&&s.done())){_tutShown=false;_tutI++;_tutT=1.4;}
}
function tutHint(html){
  const h=$("#hint");h.innerHTML=html;h.classList.add("on");
  clearTimeout(_hintT);_hintT=setTimeout(()=>h.classList.remove("on"),11000);
}

/* ── HUD baselines ────────────────────────────────────────────────────── */
function syncResBaseline(){
  for(const r of RESDEF){
    _lastRes[r.k]=G.stock[r.k]|0;
    const e=$('.res[data-k="'+r.k+'"]');
    if(e){e.querySelector(".v").textContent=fmt(_lastRes[r.k]);e.classList.remove("flash","neg");}
  }
}
let _menuSig="";
function menuSig(){let s="";for(const k of BORDER)s+=canAfford(BDEF[k].cost)?"1":"0";return s;}

/* ── button wiring ────────────────────────────────────────────────────── */
$("#btnNew").onclick=()=>{Audio_.init();Audio_.uiBig();startGame($("#seedInput").value.trim(),_modeSel);};
$("#goalbar").onclick=()=>{Audio_.init();Audio_.ui();openObjectives();};
$("#btnContinue").onclick=()=>{
  Audio_.init();Audio_.uiBig();
  if(!loadGame())notify("Sem partida salva","Comece uma nova colônia.","bad");
};
$("#btnRoll").onclick=()=>{Audio_.init();Audio_.ui();$("#seedInput").value=randSeedWord();};
$("#seedInput").addEventListener("keydown",e=>{
  if(e.key==="Enter"){e.preventDefault();$("#btnNew").click();}
  e.stopPropagation();
});
window.addEventListener("beforeunload",()=>{if(G.started&&!G.over&&MD().autosave)saveGame();});
document.addEventListener("visibilitychange",()=>{
  if(document.hidden){if(G.started&&!G.over){G.t.paused=true;syncSpeedUI();if(MD().autosave)saveGame();}}
});
window.addEventListener("resize",()=>{resizeLight();});

/* ── main loop ────────────────────────────────────────────────────────── */
let _last=performance.now(),_hudT=0,_uiT=0,_ambT=0;
function frame(now){
  requestAnimationFrame(frame);
  let rdt=(now-_last)/1000; _last=now;
  if(!isFinite(rdt)||rdt<0)rdt=0;
  rdt=Math.min(rdt,0.1);
  const T=now/1000;

  if(G.started){
    updateCamera(rdt);
    if(!G.t.paused&&!G.over){
      G.t.elapsed+=rdt;
      simulate(rdt*SPEEDS[clamp(G.t.speed|0,1,3)]);
    }
    _ambT-=rdt;
    if(_ambT<=0){
      _ambT=0.45;
      const w=G.wx.type;
      Audio_.setRain(w==="storm"?1:w==="rain"?.72:w==="snow"?.3:w==="fog"?.15:.045);
    }
    _hudT-=rdt;
    if(_hudT<=0){_hudT=0.1;updateHUD(rdt);tutorialTick(0.1);}
    _uiT-=rdt;
    if(_uiT<=0){
      _uiT=0.34;
      const ms=menuSig();
      if(ms!==_menuSig){_menuSig=ms;buildMenu();}
      if(!$("#modalwrap").classList.contains("on"))renderRight();
    }
    _autoT-=rdt;
    if(_autoT<=0){_autoT=20;autosave();}
    drawMinimap(T,rdt);
    render(T,rdt);
  }
}

/* ── boot ─────────────────────────────────────────────────────────────── */
showTitle();
requestAnimationFrame(frame);
