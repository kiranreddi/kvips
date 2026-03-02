/* KVIPS — main.js v2.0 */
(function () {
    'use strict';

    /* ---------- Mobile nav toggle ---------- */
    const toggle = document.querySelector('.navbar-toggle');
    const menu = document.querySelector('.navbar-links');
    if (toggle && menu) {
        toggle.addEventListener('click', () => menu.classList.toggle('open'));
        document.addEventListener('click', (e) => {
            if (!toggle.contains(e.target) && !menu.contains(e.target)) menu.classList.remove('open');
        });
    }

    /* ---------- Navbar scroll shadow ---------- */
    const navbar = document.querySelector('.navbar');
    if (navbar) {
        const mark = () => navbar.classList.toggle('scrolled', window.scrollY > 20);
        window.addEventListener('scroll', mark, { passive: true });
        mark();
    }

    /* ---------- Tabs ---------- */
    document.querySelectorAll('.code-tabs').forEach((tabs) => {
        const btns = tabs.querySelectorAll('.tab-btn');
        const panels = tabs.querySelectorAll('.tab-panel');
        btns.forEach((btn) => {
            btn.addEventListener('click', () => {
                const id = btn.dataset.tab;
                btns.forEach(b => b.classList.toggle('active', b === btn));
                panels.forEach(p => p.classList.toggle('active', p.dataset.tab === id));
            });
            /* Keyboard a11y */
            btn.addEventListener('keydown', (e) => {
                const arr = Array.from(btns);
                let idx = arr.indexOf(btn);
                if (e.key === 'ArrowRight') { idx = (idx + 1) % arr.length; arr[idx].focus(); arr[idx].click(); }
                if (e.key === 'ArrowLeft') { idx = (idx - 1 + arr.length) % arr.length; arr[idx].focus(); arr[idx].click(); }
            });
        });
    });

    /* ---------- Smooth anchor scroll ---------- */
    document.querySelectorAll('a[href^="#"]').forEach((a) => {
        a.addEventListener('click', (e) => {
            const target = document.querySelector(a.getAttribute('href'));
            if (target) { e.preventDefault(); target.scrollIntoView({ behavior: 'smooth', block: 'start' }); }
        });
    });

    /* ---------- Code copy buttons ---------- */
    document.querySelectorAll('.code-block pre, .code-tabs pre').forEach((pre) => {
        const btn = document.createElement('button');
        btn.className = 'copy-btn';
        btn.textContent = 'Copy';
        btn.setAttribute('aria-label', 'Copy code');
        Object.assign(btn.style, {
            position: 'absolute', top: '.5rem', right: '.5rem',
            padding: '.25rem .625rem', fontSize: '.7rem', fontWeight: '600',
            border: '1px solid rgba(255,255,255,.15)', borderRadius: '4px',
            background: 'rgba(255,255,255,.08)', color: '#ccc', cursor: 'pointer',
            transition: 'all 150ms ease'
        });
        btn.addEventListener('mouseenter', () => { btn.style.background = 'rgba(255,255,255,.15)'; });
        btn.addEventListener('mouseleave', () => { btn.style.background = 'rgba(255,255,255,.08)'; });
        btn.addEventListener('click', () => {
            navigator.clipboard.writeText(pre.textContent).then(() => {
                btn.textContent = 'Copied!';
                setTimeout(() => { btn.textContent = 'Copy'; }, 1500);
            });
        });
        const wrapper = pre.closest('.code-block') || pre.closest('.tab-panel') || pre.parentNode;
        wrapper.style.position = 'relative';
        wrapper.appendChild(btn);
    });

    /* ---------- Scroll-to-top ---------- */
    const stt = document.querySelector('.scroll-top');
    if (stt) {
        window.addEventListener('scroll', () => stt.classList.toggle('show', window.scrollY > 400), { passive: true });
        stt.addEventListener('click', () => window.scrollTo({ top: 0, behavior: 'smooth' }));
    }

    /* ---------- Active nav link ---------- */
    const path = window.location.pathname;
    document.querySelectorAll('.navbar-links a').forEach((a) => {
        const href = a.getAttribute('href');
        if (href && !href.startsWith('http') && path.indexOf(href) === 0 && href !== '/') {
            a.classList.add('active');
        }
    });

    /* ---------- External link target ---------- */
    document.querySelectorAll('a[href^="http"]').forEach((a) => {
        if (!a.hostname || a.hostname !== window.location.hostname) {
            a.setAttribute('target', '_blank');
            a.setAttribute('rel', 'noopener');
        }
    });
})();
