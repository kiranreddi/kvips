# GitHub Pages Deployment Guide

This document provides step-by-step instructions for deploying the KVIPS documentation site to GitHub Pages.

## Prerequisites

- Repository hosted on GitHub
- GitHub Pages enabled for your repository
- Admin access to repository settings

---

## 🚀 Automated Deployment (Recommended)

### Step 1: Enable GitHub Pages

1. Go to your repository on GitHub
2. Click **Settings** → **Pages**
3. Under "Source", select **GitHub Actions**
4. Save the changes

### Step 2: Push to GitHub

The GitHub Actions workflow (`.github/workflows/pages.yml`) will automatically build and deploy your site when you push to the `main` or `master` branch.

```bash
# Add all GitHub Pages files
git add _config.yml Gemfile index.html docs/ assets/ _layouts/

# Commit
git commit -m "Add GitHub Pages site with premium UI"

# Push to main branch
git push origin main
```

### Step 3: Verify Deployment

1. Go to **Actions** tab in your repository
2. You should see a workflow run for "Deploy GitHub Pages"
3. Wait for the workflow to complete (usually 2-3 minutes)
4. Visit `https://kiranreddi.github.io/kvips/`

---

## 🔧 Manual Setup (Alternative)

If you prefer manual setup or need to troubleshoot:

### Step 1: Install Jekyll Locally

```bash
# Install Ruby (if not already installed)
# On Ubuntu/Debian:
sudo apt-get install ruby-full build-essential zlib1g-dev

# On macOS:
brew install ruby

# Install Bundler
gem install bundler

# Navigate to your repository
cd kvips

# Install dependencies
bundle install
```

### Step 2: Test Locally

```bash
# Build and serve the site locally
bundle exec jekyll serve

# Or with live reload:
bundle exec jekyll serve --livereload

# Open browser to http://localhost:4000
```

### Step 3: Build for Production

```bash
# Build the site
bundle exec jekyll build

# Output will be in _site/ directory
```

### Step 4: Deploy to GitHub Pages

**Option A: Using GitHub Actions (see Automated Deployment above)**

**Option B: Using gh-pages branch**

```bash
# Install gh-pages gem
gem install github-pages

# Build site
bundle exec jekyll build

# Create gh-pages branch (first time only)
git checkout --orphan gh-pages
git rm -rf .
cp -r _site/* .
git add .
git commit -m "Deploy GitHub Pages"
git push origin gh-pages

# Configure GitHub Pages to use gh-pages branch
# Go to Settings → Pages → Source → Branch: gh-pages
```

---

## 📝 Configuration

### Update Site URLs

Edit `_config.yml` and update these fields:

```yaml
title: KVIPS
description: Your description
baseurl: "" # For user/org pages: leave empty
            # For project pages: "/repository-name"
url: "" # Will be set automatically by GitHub Pages

# Update navigation URLs if using project pages
navigation:
  - title: Home
    url: /repository-name/  # Add baseurl prefix if needed
```

### Update GitHub Links

Replace `kiranreddi` with your actual GitHub username in:

1. `index.html`
2. `docs/*.md`
3. `_layouts/default.html`
4. `README_GITHUB_PAGES.md`

You can do this with a simple find-replace:

```bash
# On Linux/macOS:
find . -type f \( -name "*.html" -o -name "*.md" \) \
  -exec sed -i 's/kiranreddi/your-actual-username/g' {} +

# On macOS with BSD sed:
find . -type f \( -name "*.html" -o -name "*.md" \) \
  -exec sed -i '' 's/kiranreddi/your-actual-username/g' {} +
```

---

## 🎨 Customization

### Change Color Scheme

Edit `assets/css/style.css` and modify CSS variables:

```css
:root {
  --primary-color: #2563eb;     /* Change to your brand color */
  --secondary-color: #8b5cf6;   /* Secondary accent */
  --accent-color: #10b981;       /* Success/accent color */
  /* ... */
}
```

### Add Custom Logo

1. Add your logo to `assets/images/logo.svg`
2. Update `.navbar-logo` in `_layouts/default.html`:

```html
<a href="{{ '/' | relative_url }}" class="navbar-logo">
  <img src="{{ '/assets/images/logo.svg' | relative_url }}" alt="KVIPS" height="32">
</a>
```

### Add Analytics

Edit `_config.yml` and add:

```yaml
google_analytics: UA-XXXXXXXXX-X
```

Or use Google Tag Manager in `_layouts/default.html`.

---

## 🔍 Troubleshooting

### Build Fails with Dependency Errors

```bash
# Clean and reinstall
rm Gemfile.lock
bundle install
bundle exec jekyll build
```

### Pages Not Updating

1. Check Actions tab for build errors
2. Clear browser cache
3. Try incognito/private browsing mode
4. Wait 5-10 minutes for GitHub CDN to update

### 404 Errors on Navigation

- Check `baseurl` in `_config.yml`
- Ensure all internal links use `{{ | relative_url }}` filter
- Verify permalink structure in front matter

### CSS Not Loading

- Check file paths in `_layouts/default.html`
- Ensure `assets/css/style.css` exists
- Check browser console for 404 errors
- Clear browser cache

### Local Build Works but GitHub Pages Fails

- Check GitHub Pages build log in Actions
- Ensure all plugins are in `_config.yml` plugins list
- Use only GitHub Pages approved plugins
- Check for unsupported Jekyll features

---

## 📦 File Checklist

Ensure these files exist:

```
✅ _config.yml              # Jekyll configuration
✅ Gemfile                  # Ruby dependencies
✅ index.html               # Homepage
✅ _layouts/default.html    # Page template
✅ assets/css/style.css     # Styling
✅ assets/js/main.js        # JavaScript
✅ docs/getting-started.md  # Documentation
✅ docs/code-review.md      # Code review
✅ docs/axi4-vip.md         # VIP docs
✅ docs/best-practices.md   # Best practices
✅ .github/workflows/pages.yml  # GitHub Actions workflow
```

---

## 🚦 Deployment Status

Check deployment status:

1. **Actions Tab**: See build/deploy workflow status
2. **Settings → Pages**: See deployment URL and status
3. **Commits**: See deployment checks on commits

Green checkmark (✅) = successful deployment
Red X (❌) = failed deployment (click for details)

---

## 📈 Post-Deployment

### Set Up Custom Domain (Optional)

1. Add `CNAME` file to repository root:
   ```
   docs.yourproject.com
   ```

2. Configure DNS:
   ```
   CNAME record: docs → kiranreddi.github.io
   ```

3. Enable HTTPS in Settings → Pages

### Monitor Traffic

Enable Google Analytics or GitHub Insights:
- Settings → Insights → Traffic
- See visitors, popular pages, referrers

### Keep Updated

```bash
# Regularly update dependencies
bundle update

# Test locally before pushing
bundle exec jekyll serve

# Commit and push updates
git add .
git commit -m "Update documentation"
git push origin main
```

---

## 🆘 Getting Help

If you encounter issues:

1. **Check Jekyll docs**: https://jekyllrb.com/docs/
2. **GitHub Pages docs**: https://docs.github.com/en/pages
3. **Open an issue**: https://github.com/kiranreddi/kvips/issues
4. **Search community**: https://github.community/

---

## ✅ Success Criteria

Your site is successfully deployed when:

- ✅ `https://kiranreddi.github.io/kvips/` loads without errors
- ✅ All navigation links work
- ✅ CSS styling applied correctly
- ✅ JavaScript features functional
- ✅ Documentation pages accessible
- ✅ Code syntax highlighting works
- ✅ Responsive design on mobile

---

<div align="center">
<strong>🎉 Congratulations on deploying your premium documentation site! 🎉</strong>
</div>
