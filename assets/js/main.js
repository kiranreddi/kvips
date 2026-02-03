/**
 * KVIPS - Premium Verification IP Library
 * Main JavaScript for Enhanced Interactions
 * Version: 1.0
 */

(function () {
    'use strict';

    // ==========================================
    // Mobile Navigation Toggle
    // ==========================================
    function initMobileNav() {
        const toggle = document.querySelector('.navbar-toggle');
        const menu = document.querySelector('.navbar-menu');

        if (toggle && menu) {
            toggle.addEventListener('click', function () {
                menu.classList.toggle('active');
                toggle.classList.toggle('active');

                // Accessibility
                const expanded = toggle.getAttribute('aria-expanded') === 'true';
                toggle.setAttribute('aria-expanded', !expanded);
            });

            // Close menu when clicking outside
            document.addEventListener('click', function (e) {
                if (!toggle.contains(e.target) && !menu.contains(e.target)) {
                    menu.classList.remove('active');
                    toggle.classList.remove('active');
                    toggle.setAttribute('aria-expanded', 'false');
                }
            });

            // Close menu on escape key
            document.addEventListener('keydown', function (e) {
                if (e.key === 'Escape' && menu.classList.contains('active')) {
                    menu.classList.remove('active');
                    toggle.classList.remove('active');
                    toggle.setAttribute('aria-expanded', 'false');
                }
            });
        }
    }

    // ==========================================
    // Tab Functionality
    // ==========================================
    function initTabs() {
        const tabButtons = document.querySelectorAll('.tab-button');
        const tabContents = document.querySelectorAll('.tab-content');

        tabButtons.forEach(function (button) {
            button.addEventListener('click', function () {
                const tabName = this.getAttribute('data-tab');

                // Remove active class from all buttons and contents
                tabButtons.forEach(function (btn) {
                    btn.classList.remove('active');
                });
                tabContents.forEach(function (content) {
                    content.classList.remove('active');
                });

                // Add active class to clicked button and corresponding content
                this.classList.add('active');
                const activeContent = document.querySelector('.tab-content[data-tab="' + tabName + '"]');
                if (activeContent) {
                    activeContent.classList.add('active');
                }

                // Accessibility
                tabButtons.forEach(function (btn) {
                    btn.setAttribute('aria-selected', 'false');
                    btn.setAttribute('tabindex', '-1');
                });
                this.setAttribute('aria-selected', 'true');
                this.setAttribute('tabindex', '0');
            });

            // Keyboard navigation for tabs
            button.addEventListener('keydown', function (e) {
                let index = Array.from(tabButtons).indexOf(this);

                if (e.key === 'ArrowRight') {
                    e.preventDefault();
                    index = (index + 1) % tabButtons.length;
                    tabButtons[index].click();
                    tabButtons[index].focus();
                } else if (e.key === 'ArrowLeft') {
                    e.preventDefault();
                    index = (index - 1 + tabButtons.length) % tabButtons.length;
                    tabButtons[index].click();
                    tabButtons[index].focus();
                }
            });
        });
    }

    // ==========================================
    // Smooth Scroll for Anchor Links
    // ==========================================
    function initSmoothScroll() {
        const links = document.querySelectorAll('a[href^="#"]');

        links.forEach(function (link) {
            link.addEventListener('click', function (e) {
                const href = this.getAttribute('href');

                if (href !== '#') {
                    const target = document.querySelector(href);

                    if (target) {
                        e.preventDefault();
                        const navbarHeight = document.querySelector('.navbar')?.offsetHeight || 0;
                        const targetPosition = target.getBoundingClientRect().top + window.pageYOffset - navbarHeight - 20;

                        window.scrollTo({
                            top: targetPosition,
                            behavior: 'smooth'
                        });

                        // Update focus for accessibility
                        target.setAttribute('tabindex', '-1');
                        target.focus();
                    }
                }
            });
        });
    }

    // ==========================================
    // Code Copy Functionality
    // ==========================================
    function initCodeCopy() {
        const codeBlocks = document.querySelectorAll('pre code');

        codeBlocks.forEach(function (codeBlock) {
            const pre = codeBlock.parentElement;

            // Create copy button
            const copyButton = document.createElement('button');
            copyButton.className = 'code-copy-btn';
            copyButton.innerHTML = '📋 Copy';
            copyButton.setAttribute('aria-label', 'Copy code to clipboard');

            // Style the button
            Object.assign(copyButton.style, {
                position: 'absolute',
                top: '0.5rem',
                right: '0.5rem',
                padding: '0.5rem 1rem',
                background: 'rgba(255, 255, 255, 0.1)',
                color: 'white',
                border: '1px solid rgba(255, 255, 255, 0.2)',
                borderRadius: '0.5rem',
                cursor: 'pointer',
                fontSize: '0.875rem',
                fontWeight: '600',
                transition: 'all 0.2s',
                zIndex: '10'
            });

            // Position the pre element
            pre.style.position = 'relative';

            // Hover effect
            copyButton.addEventListener('mouseenter', function () {
                this.style.background = 'rgba(255, 255, 255, 0.2)';
            });
            copyButton.addEventListener('mouseleave', function () {
                this.style.background = 'rgba(255, 255, 255, 0.1)';
            });

            // Copy functionality
            copyButton.addEventListener('click', function () {
                const code = codeBlock.textContent;

                navigator.clipboard.writeText(code).then(function () {
                    copyButton.innerHTML = '✓ Copied!';
                    copyButton.style.background = 'rgba(16, 185, 129, 0.2)';

                    setTimeout(function () {
                        copyButton.innerHTML = '📋 Copy';
                        copyButton.style.background = 'rgba(255, 255, 255, 0.1)';
                    }, 2000);
                }).catch(function (err) {
                    console.error('Failed to copy code:', err);
                    copyButton.innerHTML = '✗ Failed';

                    setTimeout(function () {
                        copyButton.innerHTML = '📋 Copy';
                    }, 2000);
                });
            });

            pre.appendChild(copyButton);
        });
    }

    // ==========================================
    // Navbar State and Active Highlighting
    // ==========================================
    function initNavbar() {
        const navbar = document.querySelector('.navbar');
        const navLinks = document.querySelectorAll('.nav-link');
        const currentPath = window.location.pathname;

        // active class on scroll
        window.addEventListener('scroll', function() {
            if (window.scrollY > 50) {
                navbar.classList.add('scrolled');
            } else {
                navbar.classList.remove('scrolled');
            }
        });

        // Highlight active link
        navLinks.forEach(link => {
            const href = link.getAttribute('href');
            if (href && (currentPath === href || currentPath === href + '/' || currentPath === href.replace('index.html', ''))) {
                link.classList.add('active');
            }
        });
    }

    // ==========================================
    // Scroll to Top Button
    // ==========================================
    function initScrollToTop() {
        const scrollBtn = document.createElement('button');
        scrollBtn.className = 'scroll-to-top';
        scrollBtn.innerHTML = '↑';
        scrollBtn.setAttribute('aria-label', 'Scroll to top');

        // Style the button
        Object.assign(scrollBtn.style, {
            position: 'fixed',
            bottom: '2rem',
            right: '2rem',
            width: '3rem',
            height: '3rem',
            background: 'linear-gradient(135deg, #2563eb 0%, #8b5cf6 100%)',
            color: 'white',
            border: 'none',
            borderRadius: '50%',
            fontSize: '1.5rem',
            fontWeight: '700',
            cursor: 'pointer',
            boxShadow: '0 4px 6px -1px rgba(0, 0, 0, 0.1)',
            opacity: '0',
            visibility: 'hidden',
            transition: 'all 0.3s',
            zIndex: '1000'
        });

        // Add to page
        document.body.appendChild(scrollBtn);

        // Show/hide based on scroll position
        function checkScroll() {
            if (window.pageYOffset > 500) {
                scrollBtn.style.opacity = '1';
                scrollBtn.style.visibility = 'visible';
            } else {
                scrollBtn.style.opacity = '0';
                scrollBtn.style.visibility = 'hidden';
            }
        }

        window.addEventListener('scroll', checkScroll);

        // Scroll to top on click
        scrollBtn.addEventListener('click', function () {
            window.scrollTo({
                top: 0,
                behavior: 'smooth'
            });
        });

        // Hover effect
        scrollBtn.addEventListener('mouseenter', function () {
            this.style.transform = 'translateY(-4px)';
            this.style.boxShadow = '0 10px 15px -3px rgba(0, 0, 0, 0.2)';
        });
        scrollBtn.addEventListener('mouseleave', function () {
            this.style.transform = 'translateY(0)';
            this.style.boxShadow = '0 4px 6px -1px rgba(0, 0, 0, 0.1)';
        });
    }

    // ==========================================
    // Fade In Animation on Scroll
    // ==========================================
    function initScrollAnimations() {
        // Disabled to prevent content disappearing
        // Elements will be visible immediately without scroll animations
        return;

        const observerOptions = {
            root: null,
            rootMargin: '0px',
            threshold: 0.1
        };

        const observer = new IntersectionObserver(function (entries) {
            entries.forEach(function (entry) {
                if (entry.isIntersecting) {
                    entry.target.classList.add('fade-in');
                    observer.unobserve(entry.target);
                }
            });
        }, observerOptions);

        // Observe elements
        const animatedElements = document.querySelectorAll('.feature-item, .vip-card, .highlight-card, .stat-item');
        animatedElements.forEach(function (el) {
            el.style.opacity = '0';
            observer.observe(el);
        });
    }

    // ==========================================
    // Active Navigation Link
    // ==========================================
    function initActiveNavLink() {
        const navLinks = document.querySelectorAll('.nav-link');
        const currentPath = window.location.pathname;

        navLinks.forEach(function (link) {
            const linkPath = link.getAttribute('href');

            if (linkPath && currentPath.includes(linkPath) && linkPath !== '/') {
                link.classList.add('active');
            } else if (linkPath === '/' && currentPath === '/') {
                link.classList.add('active');
            }
        });
    }

    // ==========================================
    // External Links - Open in New Tab
    // ==========================================
    function initExternalLinks() {
        const links = document.querySelectorAll('a[href^="http"]');

        links.forEach(function (link) {
            if (!link.hostname.includes(window.location.hostname)) {
                link.setAttribute('target', '_blank');
                link.setAttribute('rel', 'noopener noreferrer');
            }
        });
    }

    // ==========================================
    // Performance: Lazy Load Images
    // ==========================================
    function initLazyLoad() {
        if ('IntersectionObserver' in window) {
            const imageObserver = new IntersectionObserver(function (entries, observer) {
                entries.forEach(function (entry) {
                    if (entry.isIntersecting) {
                        const img = entry.target;
                        img.src = img.dataset.src;
                        img.classList.remove('lazy');
                        imageObserver.unobserve(img);
                    }
                });
            });

            const images = document.querySelectorAll('img.lazy');
            images.forEach(function (img) {
                imageObserver.observe(img);
            });
        }
    }

    // ==========================================
    // Initialize All Functions
    // ==========================================
    function init() {
        // Wait for DOM to be fully loaded
        if (document.readyState === 'loading') {
            document.addEventListener('DOMContentLoaded', function () {
                runInitializers();
            });
        } else {
            runInitializers();
        }
    }

    function runInitializers() {
        initMobileNav();
        initTabs();
        initSmoothScroll();
        initCodeCopy();
        initScrollToTop();
        initScrollAnimations();
        initActiveNavLink();
        initExternalLinks();
        initLazyLoad();

        // Log initialization
        console.log('✨ KVIPS Website initialized successfully');
    }

    // Start initialization
    init();

})();
