// KVIPS - Premium Interactive Features
// Main JavaScript for GitHub Pages

document.addEventListener('DOMContentLoaded', function () {
    initSmoothScroll();
    initCodeCopyButtons();
    initSearchFunctionality();
    initMobileMenu();
    initThemeToggle();
    initAnimations();
    initTableOfContents();
    initTabSwitcher();
});

// Smooth Scroll for Anchor Links
function initSmoothScroll() {
    document.querySelectorAll('a[href^="#"]').forEach(anchor => {
        anchor.addEventListener('click', function (e) {
            const href = this.getAttribute('href');
            if (href !== '#') {
                e.preventDefault();
                const target = document.querySelector(href);
                if (target) {
                    target.scrollIntoView({
                        behavior: 'smooth',
                        block: 'start'
                    });
                    // Update URL without jumping
                    history.pushState(null, null, href);
                }
            }
        });
    });
}

// Code Copy Buttons
function initCodeCopyButtons() {
    document.querySelectorAll('pre code').forEach((block) => {
        const pre = block.parentElement;
        const wrapper = document.createElement('div');
        wrapper.className = 'code-wrapper';

        const header = document.createElement('div');
        header.className = 'code-header';

        const language = block.className.match(/language-(\w+)/);
        const langLabel = document.createElement('span');
        langLabel.textContent = language ? language[1].toUpperCase() : 'CODE';

        const copyBtn = document.createElement('button');
        copyBtn.className = 'copy-code-btn';
        copyBtn.textContent = 'Copy';
        copyBtn.addEventListener('click', () => {
            const code = block.textContent;
            navigator.clipboard.writeText(code).then(() => {
                copyBtn.textContent = 'Copied!';
                copyBtn.style.background = '#10b981';
                setTimeout(() => {
                    copyBtn.textContent = 'Copy';
                    copyBtn.style.background = '';
                }, 2000);
            });
        });

        header.appendChild(langLabel);
        header.appendChild(copyBtn);

        pre.parentNode.insertBefore(wrapper, pre);
        wrapper.appendChild(header);
        wrapper.appendChild(pre);
    });
}

// Search Functionality
function initSearchFunctionality() {
    const searchInput = document.getElementById('search-input');
    if (!searchInput) return;

    let searchIndex = [];
    let searchData = [];

    // Fetch search index (you'll need to generate this)
    fetch('/search-index.json')
        .then(response => response.json())
        .then(data => {
            searchData = data;
            buildSearchIndex(data);
        })
        .catch(err => console.log('Search index not found'));

    function buildSearchIndex(data) {
        searchIndex = data.map(item => ({
            title: item.title.toLowerCase(),
            content: item.content.toLowerCase(),
            url: item.url,
            category: item.category
        }));
    }

    searchInput.addEventListener('input', debounce(function (e) {
        const query = e.target.value.toLowerCase();
        if (query.length < 2) {
            hideSearchResults();
            return;
        }

        const results = searchIndex.filter(item =>
            item.title.includes(query) || item.content.includes(query)
        ).slice(0, 10);

        displaySearchResults(results, query);
    }, 300));

    function displaySearchResults(results, query) {
        let resultsContainer = document.getElementById('search-results');
        if (!resultsContainer) {
            resultsContainer = document.createElement('div');
            resultsContainer.id = 'search-results';
            resultsContainer.className = 'search-results';
            searchInput.parentNode.appendChild(resultsContainer);
        }

        if (results.length === 0) {
            resultsContainer.innerHTML = '<div class="search-result-item">No results found</div>';
            resultsContainer.style.display = 'block';
            return;
        }

        resultsContainer.innerHTML = results.map(result => `
      <a href="${result.url}" class="search-result-item">
        <div class="search-result-title">${highlightMatch(result.title, query)}</div>
        <div class="search-result-category">${result.category}</div>
      </a>
    `).join('');

        resultsContainer.style.display = 'block';
    }

    function hideSearchResults() {
        const resultsContainer = document.getElementById('search-results');
        if (resultsContainer) {
            resultsContainer.style.display = 'none';
        }
    }

    function highlightMatch(text, query) {
        const regex = new RegExp(`(${query})`, 'gi');
        return text.replace(regex, '<mark>$1</mark>');
    }

    // Close search results when clicking outside
    document.addEventListener('click', function (e) {
        if (!e.target.closest('.search-container')) {
            hideSearchResults();
        }
    });
}

// Mobile Menu Toggle
function initMobileMenu() {
    const menuToggle = document.createElement('button');
    menuToggle.className = 'mobile-menu-toggle';
    menuToggle.innerHTML = '☰';
    menuToggle.setAttribute('aria-label', 'Toggle menu');

    const navbar = document.querySelector('.navbar-container');
    const menu = document.querySelector('.navbar-menu');

    if (navbar && menu) {
        navbar.insertBefore(menuToggle, menu);

        menuToggle.addEventListener('click', () => {
            menu.classList.toggle('active');
            menuToggle.innerHTML = menu.classList.contains('active') ? '✕' : '☰';
        });
    }
}

// Theme Toggle (Dark/Light Mode)
function initThemeToggle() {
    const themeToggle = document.createElement('button');
    themeToggle.className = 'theme-toggle';
    themeToggle.setAttribute('aria-label', 'Toggle theme');

    const savedTheme = localStorage.getItem('theme') || 'light';
    document.documentElement.setAttribute('data-theme', savedTheme);
    updateThemeIcon(themeToggle, savedTheme);

    themeToggle.addEventListener('click', () => {
        const currentTheme = document.documentElement.getAttribute('data-theme');
        const newTheme = currentTheme === 'dark' ? 'light' : 'dark';
        document.documentElement.setAttribute('data-theme', newTheme);
        localStorage.setItem('theme', newTheme);
        updateThemeIcon(themeToggle, newTheme);
    });

    const navbar = document.querySelector('.navbar-menu');
    if (navbar) {
        const li = document.createElement('li');
        li.appendChild(themeToggle);
        navbar.appendChild(li);
    }

    function updateThemeIcon(button, theme) {
        button.innerHTML = theme === 'dark' ? '☀️' : '🌙';
    }
}

// Scroll Animations
function initAnimations() {
    const observerOptions = {
        threshold: 0.1,
        rootMargin: '0px 0px -100px 0px'
    };

    const observer = new IntersectionObserver((entries) => {
        entries.forEach(entry => {
            if (entry.isIntersecting) {
                entry.target.classList.add('fade-in');
                observer.unobserve(entry.target);
            }
        });
    }, observerOptions);

    document.querySelectorAll('.card, .feature-item, .alert').forEach(el => {
        observer.observe(el);
    });
}

// Table of Contents Generator
function initTableOfContents() {
    const tocContainer = document.getElementById('toc');
    if (!tocContainer) return;

    const headings = document.querySelectorAll('h2, h3, h4');
    if (headings.length === 0) return;

    const toc = document.createElement('ul');
    toc.className = 'toc-list';

    headings.forEach((heading, index) => {
        // Add ID if not present
        if (!heading.id) {
            heading.id = `heading-${index}`;
        }

        const li = document.createElement('li');
        li.className = `toc-item toc-${heading.tagName.toLowerCase()}`;

        const link = document.createElement('a');
        link.href = `#${heading.id}`;
        link.textContent = heading.textContent;

        li.appendChild(link);
        toc.appendChild(li);
    });

    tocContainer.appendChild(toc);

    // Highlight current section
    window.addEventListener('scroll', debounce(() => {
        let current = '';
        headings.forEach(heading => {
            const rect = heading.getBoundingClientRect();
            if (rect.top <= 100) {
                current = heading.id;
            }
        });

        document.querySelectorAll('.toc-item a').forEach(link => {
            link.classList.remove('active');
            if (link.getAttribute('href') === `#${current}`) {
                link.classList.add('active');
            }
        });
    }, 100));
}

// Tab Switcher for Code Examples
function initTabSwitcher() {
    document.querySelectorAll('.tab-container').forEach(container => {
        const tabs = container.querySelectorAll('.tab-btn');
        const panels = container.querySelectorAll('.tab-panel');

        tabs.forEach((tab, index) => {
            tab.addEventListener('click', () => {
                tabs.forEach(t => t.classList.remove('active'));
                panels.forEach(p => p.classList.remove('active'));

                tab.classList.add('active');
                panels[index].classList.add('active');
            });
        });
    });
}

// Utility: Debounce Function
function debounce(func, wait) {
    let timeout;
    return function executedFunction(...args) {
        const later = () => {
            clearTimeout(timeout);
            func(...args);
        };
        clearTimeout(timeout);
        timeout = setTimeout(later, wait);
    };
}

// Utility: Throttle Function
function throttle(func, limit) {
    let inThrottle;
    return function (...args) {
        if (!inThrottle) {
            func.apply(this, args);
            inThrottle = true;
            setTimeout(() => inThrottle = false, limit);
        }
    };
}

// Back to Top Button
(function () {
    const backToTop = document.createElement('button');
    backToTop.className = 'back-to-top';
    backToTop.innerHTML = '↑';
    backToTop.setAttribute('aria-label', 'Back to top');
    document.body.appendChild(backToTop);

    window.addEventListener('scroll', throttle(() => {
        if (window.pageYOffset > 300) {
            backToTop.classList.add('visible');
        } else {
            backToTop.classList.remove('visible');
        }
    }, 100));

    backToTop.addEventListener('click', () => {
        window.scrollTo({
            top: 0,
            behavior: 'smooth'
        });
    });
})();

// EDA Tool Version Checker (demonstrates interactivity)
function checkToolVersion(tool, version) {
    const supportedVersions = {
        'questa': ['2024_1', '2024_2', '2025_3_2'],
        'vcs': ['2024.12', '2025.06_1'],
        'xcelium': ['24.09.001', '25.03.007']
    };

    const versions = supportedVersions[tool.toLowerCase()];
    if (!versions) return { supported: false, message: 'Unknown tool' };

    const isSupported = versions.includes(version);
    return {
        supported: isSupported,
        message: isSupported ?
            `${tool} ${version} is officially supported` :
            `${tool} ${version} may not be supported. Recommended: ${versions.join(', ')}`
    };
}

// Export for potential use in other scripts
if (typeof module !== 'undefined' && module.exports) {
    module.exports = {
        checkToolVersion,
        debounce,
        throttle
    };
}