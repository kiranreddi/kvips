# KVIPS Website

This folder contains all GitHub Pages website files for the KVIPS verification IP library.

## 📂 Structure

```
website/
├── _config.yml              # Jekyll configuration
├── _layouts/                # Page layouts
│   └── default.html        # Default layout template
├── assets/                  # Static assets
│   ├── css/                # Stylesheets
│   │   ├── style.css       # Main styles
│   │   └── components.css  # Component styles
│   ├── js/                 # JavaScript
│   │   └── main.js         # Main interactions
│   └── images/             # Images and icons
├── pages/                   # Content pages
│   ├── docs/               # Documentation pages
│   │   ├── getting-started.md
│   │   ├── axi4-vip.md
│   │   ├── best-practices.md
│   │   ├── code-review.md
│   │   └── faq.md
│   └── vips/               # VIP-specific pages
├── index.md                 # Homepage
├── Gemfile                  # Ruby dependencies
└── README.md               # This file
```

## 🚀 Local Development

### Prerequisites

- Ruby 2.7 or higher
- Bundler gem
- Jekyll 3.9 or higher

### Setup

```bash
# Navigate to website folder
cd website

# Install dependencies
bundle install

# Run local server
bundle exec jekyll serve

# View at http://localhost:4000/kvips/
```

### Development Commands

```bash
# Build the site
bundle exec jekyll build

# Serve with live reload
bundle exec jekyll serve --livereload

# Serve with drafts
bundle exec jekyll serve --drafts

# Build for production
JEKYLL_ENV=production bundle exec jekyll build
```

## 🎨 Customization

### Colors

Edit CSS variables in `assets/css/style.css`:

```css
:root {
    --primary: #2563eb;     /* Primary blue */
    --secondary: #8b5cf6;   /* Secondary purple */
    --accent: #10b981;      /* Accent green */
    /* ... more colors ... */
}
```

### Typography

Fonts are configured in `assets/css/style.css`:

```css
:root {
    --font-sans: 'Inter', sans-serif;
    --font-mono: 'JetBrains Mono', monospace;
}
```

### Navigation

Edit navigation links in `_layouts/default.html`:

```html
<ul class="navbar-menu">
    <li><a href="{{ '/' | relative_url }}" class="nav-link">Home</a></li>
    <!-- Add more links here -->
</ul>
```

## 📝 Adding Content

### New Documentation Page

1. Create a new Markdown file in `pages/docs/`:

```markdown
---
layout: default
title: Your Page Title
description: Page description
---

# Your Content Here

...
```

2. Add link to navigation in `_layouts/default.html`

### New VIP Page

1. Create file in `pages/vips/`
2. Follow the same format as documentation pages
3. Update VIP cards on homepage (`index.md`)

## 🏗️ Build & Deploy

### GitHub Pages Deployment

The site automatically deploys when you push to the `main` branch:

```bash
# Commit changes
git add website/
git commit -m "Update website"
git push origin main
```

GitHub Actions will automatically build and deploy to:
- **URL**: https://kiranreddi.github.io/kvips/

### Manual Build

```bash
cd website
JEKYLL_ENV=production bundle exec jekyll build
# Output in _site/
```

## 🎯 Features

### Premium UI Components

- ✨ **Gradient Hero Section** - Eye-catching landing
- 🎨 **Glass Morphism Effects** - Modern, translucent cards
- 🌗 **Dark Mode Support** - Automatic theme detection
- 📱 **Responsive Design** - Mobile, tablet, desktop
- ⚡ **Smooth Animations** - Scroll-triggered fade-ins
- 🔘 **Interactive Tabs** - Code examples for each simulator
- 📋 **Code Copy Buttons** - One-click code copying
- 🔝 **Scroll to Top** - Fixed bottom-right button
- 🎯 **Active Nav Links** - Highlights current page

### Performance Optimizations

- Lazy loading for images
- Minified CSS and JS (production)
- Optimized fonts loading
- Efficient animations

### Accessibility

- ARIA labels on interactive elements
- Keyboard navigation support
- Focus indicators
- Semantic HTML structure
- Screen reader friendly

## 🔧 Troubleshooting

### Site not building?

Check Jekyll logs:
```bash
bundle exec jekyll serve --verbose
```

### CSS not loading?

1. Check `_config.yml` - `baseurl` should be `/kvips`
2. Verify CSS file paths use `| relative_url` filter
3. Clear browser cache (Ctrl+Shift+R)

### JavaScript not working?

1. Check browser console for errors (F12)
2. Verify `main.js` is loaded in `_layouts/default.html`
3. Test in different browsers

### Broken links?

Use `| relative_url` filter for all internal links:
```markdown
[Link text]({{ '/pages/docs/getting-started' | relative_url }})
```

## 📊 Analytics (Optional)

To add Google Analytics, edit `_config.yml`:

```yaml
google_analytics: UA-XXXXXXXXX-X
```

## 🤝 Contributing

When contributing to the website:

1. Test locally before committing
2. Follow existing HTML/CSS/JS code style
3. Ensure responsive design (test on mobile)
4. Check accessibility (use browser dev tools)
5. Optimize images before adding

## 📚 Resources

- [Jekyll Documentation](https://jekyllrb.com/docs/)
- [Liquid Template Language](https://shopify.github.io/liquid/)
- [GitHub Pages Documentation](https://docs.github.com/en/pages)
- [Markdown Guide](https://www.markdownguide.org/)

## 🐛 Issues

Report website issues at: https://github.com/kiranreddi/kvips/issues

## 📜 License

MIT License - same as the main KVIPS project.

---

**Made with ❤️ for the verification community**
