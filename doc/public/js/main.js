document.addEventListener("DOMContentLoaded", function () {
  document.querySelectorAll(".hextra-alert[data-alert-fold]").forEach(function (alert) {
    const button = alert.querySelector(".hextra-alert-toggle");
    const content = alert.querySelector(".hextra-alert-content");
    if (!button || !content) {
      return;
    }

    const sync = function (open) {
      alert.dataset.alertFold = open ? "+" : "-";
      button.setAttribute("aria-expanded", open ? "true" : "false");
      content.setAttribute("aria-hidden", open ? "false" : "true");
      content.toggleAttribute("inert", !open);
    };

    sync(alert.dataset.alertFold === "+");

    button.addEventListener("click", function () {
      sync(alert.dataset.alertFold !== "+");
    });
  });
});

;
// Back to top button

document.addEventListener("DOMContentLoaded", function () {
  const backToTop = document.querySelector("#backToTop");
  if (backToTop) {
    backToTop.addEventListener("click", scrollUp);
    document.addEventListener("scroll", (e) => {
      if (window.scrollY > 300) {
        backToTop.classList.remove("hx:opacity-0");
        backToTop.removeAttribute("tabindex");
      } else {
        backToTop.classList.add("hx:opacity-0");
        backToTop.setAttribute("tabindex", "-1");
      }
    });
  }
});

function scrollUp() {
  const prefersReducedMotion = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  window.scroll({
    top: 0,
    left: 0,
    behavior: prefersReducedMotion ? 'auto' : 'smooth',
  });
}

;
//
;
// Copy button for code blocks

document.addEventListener('DOMContentLoaded', function () {
  const getCopyIcon = () => {
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.innerHTML = `
      <path stroke-linecap="round" stroke-linejoin="round" d="M8 16H6a2 2 0 01-2-2V6a2 2 0 012-2h8a2 2 0 012 2v2m-6 12h8a2 2 0 002-2v-8a2 2 0 00-2-2h-8a2 2 0 00-2 2v8a2 2 0 002 2z" />
    `;
    svg.setAttribute('fill', 'none');
    svg.setAttribute('viewBox', '0 0 24 24');
    svg.setAttribute('stroke', 'currentColor');
    svg.setAttribute('stroke-width', '2');
    return svg;
  }

  const getSuccessIcon = () => {
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.innerHTML = `
      <path stroke-linecap="round" stroke-linejoin="round" d="M5 13l4 4L19 7" />
    `;
    svg.setAttribute('fill', 'none');
    svg.setAttribute('viewBox', '0 0 24 24');
    svg.setAttribute('stroke', 'currentColor');
    svg.setAttribute('stroke-width', '2');
    return svg;
  }

  // Make scrollable code blocks focusable for keyboard users.
  const updateScrollableCodeBlocks = () => {
    document.querySelectorAll('.hextra-code-block pre, .highlight pre').forEach(function (pre) {
      if (pre.scrollWidth > pre.clientWidth) {
        pre.setAttribute('tabindex', '0');
      } else {
        pre.removeAttribute('tabindex');
      }
    });
  };

  updateScrollableCodeBlocks();

  let resizeRaf;
  window.addEventListener('resize', () => {
    if (resizeRaf) {
      cancelAnimationFrame(resizeRaf);
    }
    resizeRaf = requestAnimationFrame(updateScrollableCodeBlocks);
  });

  document.querySelectorAll('.hextra-code-copy-btn').forEach(function (button) {
    // Add copy and success icons
    button.querySelector('.hextra-copy-icon')?.appendChild(getCopyIcon());
    button.querySelector('.hextra-success-icon')?.appendChild(getSuccessIcon());

    // Add click event listener for copy button
    button.addEventListener('click', function (e) {
      e.preventDefault();
      // Get the code target
      const target = button.parentElement.previousElementSibling;
      let codeElement;
      if (target.tagName === 'CODE') {
        codeElement = target;
      } else {
        // Select the last code element in case line numbers are present
        const codeElements = target.querySelectorAll('code');
        codeElement = codeElements[codeElements.length - 1];
      }
      if (codeElement) {
        let code = codeElement.innerText;
        // Replace double newlines with single newlines in the innerText
        // as each line inside <span> has trailing newline '\n'
        if ("lang" in codeElement.dataset) {
          code = code.replace(/\n\n/g, '\n');
        }
        navigator.clipboard.writeText(code).then(function () {
          button.classList.add('copied');
          var originalLabel = button.getAttribute('aria-label');
          var copiedLabel = button.dataset.copiedLabel || 'Copied!';
          button.setAttribute('aria-label', copiedLabel);
          setTimeout(function () {
            button.classList.remove('copied');
            button.setAttribute('aria-label', originalLabel);
          }, 1000);
        }).catch(function (err) {
          console.error('Failed to copy text: ', err);
        });
      } else {
        console.error('Target element not found');
      }
    });
  });
});

;
// 
(function () {
  const faviconEl = document.getElementById("favicon-svg");
  const faviconDarkExists = "false" === "true";

  if (faviconEl && faviconDarkExists) {
    const lightFavicon = '/kind2_user_doc/favicon.svg';
    const darkFavicon = '/kind2_user_doc/favicon-dark.svg';

    const darkModeQuery = window.matchMedia("(prefers-color-scheme: dark)");

    function updateFavicon(e) {
      faviconEl.href = e.matches ? darkFavicon : lightFavicon;
    }

    // Set favicon on load
    updateFavicon(darkModeQuery);

    // Listen for system preference changes
    darkModeQuery.addEventListener("change", updateFavicon);
  }
})();

;
// Script for filetree shortcode collapsing/expanding folders used in the theme
// ======================================================================
document.addEventListener("DOMContentLoaded", function () {
  const folders = document.querySelectorAll(".hextra-filetree-folder");
  folders.forEach(function (folder) {
    folder.addEventListener("click", function () {
      Array.from(folder.children).forEach(function (el) {
        el.dataset.state = el.dataset.state === "open" ? "closed" : "open";
      });
      var newState = folder.nextElementSibling.dataset.state === "open" ? "closed" : "open";
      folder.nextElementSibling.dataset.state = newState;
      folder.setAttribute('aria-expanded', newState === 'open' ? 'true' : 'false');
    });
  });
});

;
(function () {
  const languageSwitchers = document.querySelectorAll('.hextra-language-switcher');
  const closeSwitcher = (switcher, focusSwitcher = false) => {
    switcher.dataset.state = 'closed';
    switcher.setAttribute('aria-expanded', 'false');
    const optionsElement = switcher.nextElementSibling;
    optionsElement.classList.add('hx:hidden');
    if (focusSwitcher) {
      switcher.focus();
    }
  };

  const openSwitcher = (switcher, focusTarget = "none") => {
    switcher.dataset.state = 'open';
    switcher.setAttribute('aria-expanded', 'true');
    const optionsElement = switcher.nextElementSibling;
    if (optionsElement.classList.contains('hx:hidden')) {
      toggleMenu(switcher);
    } else {
      resizeMenu(switcher);
    }

    if (focusTarget !== "none") {
      const items = Array.from(optionsElement.querySelectorAll('[role="menuitem"]'));
      if (items.length > 0) {
        const target = focusTarget === "last" ? items[items.length - 1] : items[0];
        target.focus();
      }
    }
  };

  languageSwitchers.forEach((switcher) => {
    switcher.addEventListener('click', (e) => {
      e.preventDefault();

      if (switcher.dataset.state === 'open') {
        closeSwitcher(switcher);
      } else {
        openSwitcher(switcher);
      }
    });

    switcher.addEventListener('keydown', (e) => {
      if (e.key === 'ArrowDown') {
        e.preventDefault();
        openSwitcher(switcher, 'first');
      } else if (e.key === 'ArrowUp') {
        e.preventDefault();
        openSwitcher(switcher, 'last');
      }
    });
  });

  document.querySelectorAll('.hextra-language-options[role=menu]').forEach((menu) => {
    menu.addEventListener('keydown', (e) => {
      const items = Array.from(menu.querySelectorAll('[role="menuitem"]'));
      if (items.length === 0) return;

      const currentIndex = items.indexOf(document.activeElement);
      let newIndex;

      switch (e.key) {
        case 'ArrowDown':
          e.preventDefault();
          newIndex = (currentIndex + 1) % items.length;
          items[newIndex].focus();
          break;
        case 'ArrowUp':
          e.preventDefault();
          newIndex = (currentIndex - 1 + items.length) % items.length;
          items[newIndex].focus();
          break;
        case 'Home':
          e.preventDefault();
          items[0].focus();
          break;
        case 'End':
          e.preventDefault();
          items[items.length - 1].focus();
          break;
        case 'Escape': {
          e.preventDefault();
          const switcher = menu.previousElementSibling;
          if (switcher) {
            closeSwitcher(switcher, true);
          }
          break;
        }
      }
    });
  });

  window.addEventListener("resize", () => languageSwitchers.forEach(resizeMenu));

  // Dismiss language switcher when clicking outside.
  document.addEventListener('click', (e) => {
    if (!e.target.closest('.hextra-language-switcher') && !e.target.closest('.hextra-language-options')) {
      languageSwitchers.forEach((switcher) => {
        closeSwitcher(switcher);
      });
    }
  });
})();

;
// Hamburger menu for mobile navigation

document.addEventListener('DOMContentLoaded', function () {
  const menu = document.querySelector('.hextra-hamburger-menu');
  const sidebarContainer = document.querySelector('.hextra-sidebar-container');
  const mobileQuery = window.matchMedia('(max-width: 767px)');

  function isMenuOpen() {
    return menu.querySelector('svg').classList.contains('open');
  }

  // On mobile, the sidebar is off-screen so hide it from assistive tech
  function syncAriaHidden() {
    if (mobileQuery.matches) {
      sidebarContainer.setAttribute('aria-hidden', isMenuOpen() ? 'false' : 'true');
    } else {
      sidebarContainer.removeAttribute('aria-hidden');
    }
  }

  // Set initial state
  syncAriaHidden();
  mobileQuery.addEventListener('change', syncAriaHidden);

  function toggleMenu(options = {}) {
    const { focusOnOpen = true } = options;

    // Toggle the hamburger menu
    menu.querySelector('svg').classList.toggle('open');

    // When the menu is open, we want to show the navigation sidebar
    sidebarContainer.classList.toggle('hx:max-md:[transform:translate3d(0,-100%,0)]');
    sidebarContainer.classList.toggle('hx:max-md:[transform:translate3d(0,0,0)]');

    // When the menu is open, we want to prevent the body from scrolling
    document.body.classList.toggle('hx:overflow-hidden');
    document.body.classList.toggle('hx:md:overflow-auto');

    // Sync aria-expanded and aria-hidden
    const isOpen = isMenuOpen();
    menu.setAttribute('aria-expanded', isOpen ? 'true' : 'false');
    syncAriaHidden();

    // Move focus into sidebar when opening, restore when closing
    if (isOpen) {
      if (focusOnOpen) {
        const firstFocusable = sidebarContainer.querySelector('a, button, input, [tabindex="0"]');
        if (firstFocusable) firstFocusable.focus();
      }
    } else {
      menu.focus();
    }
  }

  menu.addEventListener('click', (e) => {
    e.preventDefault();
    // Pointer-initiated clicks on mobile should not force focus into the search input,
    // which opens the software keyboard immediately.
    toggleMenu({ focusOnOpen: e.detail === 0 });
  });

  // Close menu on Escape key (mobile only)
  document.addEventListener('keydown', (e) => {
    if (e.key !== 'Escape') return;
    if (document.getElementById('hextra-search-dialog')?.open) return;
    if (mobileQuery.matches && isMenuOpen()) {
      toggleMenu();
    }
  });

  // Select all anchor tags in the sidebar container
  const sidebarLinks = sidebarContainer.querySelectorAll('a');

  // Add click event listener to each anchor tag
  sidebarLinks.forEach(link => {
    link.addEventListener('click', (e) => {
      // Check if the href attribute contains a hash symbol (links to a heading)
      if (link.getAttribute('href') && link.getAttribute('href').startsWith('#')) {
        // Only dismiss overlay on mobile view
        if (window.innerWidth < 768) {
          toggleMenu();
        }
      }
    });
  });
});

;
(function () {
  const hiddenClass = "hx:hidden";
  const dropdownToggles = document.querySelectorAll(".hextra-nav-menu-toggle");
  const closeDropdown = (toggle, focusToggle = false) => {
    toggle.dataset.state = "closed";
    toggle.setAttribute("aria-expanded", "false");
    const menuItemsElement = toggle.nextElementSibling;
    menuItemsElement.classList.add(hiddenClass);
    if (focusToggle) {
      toggle.focus();
    }
  };

  const openDropdown = (toggle, focusTarget = "none") => {
    // Close all other dropdowns first.
    dropdownToggles.forEach((otherToggle) => {
      if (otherToggle !== toggle) {
        closeDropdown(otherToggle);
      }
    });

    toggle.dataset.state = "open";
    toggle.setAttribute("aria-expanded", "true");
    const menuItemsElement = toggle.nextElementSibling;

    // Position dropdown centered with toggle.
    menuItemsElement.style.position = "absolute";
    menuItemsElement.style.top = "100%";
    menuItemsElement.style.left = "50%";
    menuItemsElement.style.transform = "translateX(-50%)";
    menuItemsElement.style.zIndex = "1000";
    menuItemsElement.classList.remove(hiddenClass);

    if (focusTarget !== "none") {
      const items = Array.from(menuItemsElement.querySelectorAll('[role="menuitem"]'));
      if (items.length > 0) {
        const target = focusTarget === "last" ? items[items.length - 1] : items[0];
        target.focus();
      }
    }
  };

  dropdownToggles.forEach((toggle) => {
    toggle.addEventListener("click", (e) => {
      e.preventDefault();
      e.stopPropagation();

      // Toggle current dropdown.
      const isOpen = toggle.dataset.state === "open";
      if (isOpen) {
        closeDropdown(toggle);
      } else {
        openDropdown(toggle);
      }
    });

    toggle.addEventListener("keydown", (e) => {
      if (e.key === "ArrowDown") {
        e.preventDefault();
        openDropdown(toggle, "first");
      } else if (e.key === "ArrowUp") {
        e.preventDefault();
        openDropdown(toggle, "last");
      }
    });
  });

  document.querySelectorAll(".hextra-nav-menu-items[role=menu]").forEach((menu) => {
    menu.addEventListener("keydown", (e) => {
      const items = Array.from(menu.querySelectorAll('[role="menuitem"]'));
      if (items.length === 0) return;

      const currentIndex = items.indexOf(document.activeElement);
      let newIndex;

      switch (e.key) {
        case "ArrowDown":
          e.preventDefault();
          newIndex = (currentIndex + 1) % items.length;
          items[newIndex].focus();
          break;
        case "ArrowUp":
          e.preventDefault();
          newIndex = (currentIndex - 1 + items.length) % items.length;
          items[newIndex].focus();
          break;
        case "Home":
          e.preventDefault();
          items[0].focus();
          break;
        case "End":
          e.preventDefault();
          items[items.length - 1].focus();
          break;
        case "Escape": {
          e.preventDefault();
          const toggle = menu.previousElementSibling;
          if (toggle) {
            closeDropdown(toggle, true);
          }
          break;
        }
      }
    });
  });

  // Dismiss dropdown when clicking outside.
  document.addEventListener("click", (e) => {
    if (!e.target.closest(".hextra-nav-menu-toggle") && !e.target.closest(".hextra-nav-menu-items")) {
      dropdownToggles.forEach((toggle) => {
        closeDropdown(toggle);
      });
    }
  });

  // Close dropdowns on escape key.
  document.addEventListener("keydown", (e) => {
    if (e.key === "Escape") {
      dropdownToggles.forEach((toggle) => {
        if (toggle.dataset.state === "open") {
          closeDropdown(toggle, true);
        }
      });
    }
  });
})();

;
document.addEventListener('DOMContentLoaded', () => {
  // Pre-fetch markdown content for all copy buttons to avoid Safari NotAllowedError
  // Safari requires clipboard writes to happen synchronously within user gesture
  const copyButtons = document.querySelectorAll('.hextra-page-context-menu-copy');
  const contentCache = new Map();

  // Pre-fetch content for each button on page load
  copyButtons.forEach(button => {
    const url = button.dataset.url;
    if (url) {
      fetch(url)
        .then(response => {
          if (response.ok) return response.text();
          throw new Error('Failed to fetch');
        })
        .then(markdown => contentCache.set(url, markdown))
        .catch(error => console.error('Failed to pre-fetch markdown:', error));
    }
  });

  // Initialize copy buttons with synchronous clipboard access
  copyButtons.forEach(button => {
    button.addEventListener('click', () => {
      const url = button.dataset.url;
      const markdown = contentCache.get(url);

      if (markdown) {
        // Synchronous clipboard write initiation - works in Safari
        navigator.clipboard.writeText(markdown)
          .then(() => {
            button.classList.add('copied');
            setTimeout(() => button.classList.remove('copied'), 1000);
          })
          .catch(error => console.error('Failed to copy markdown:', error));
      } else {
        // Fallback: fetch and copy (may fail in Safari if content not pre-fetched)
        fetch(url)
          .then(response => {
            if (!response.ok) throw new Error('Failed to fetch');
            return response.text();
          })
          .then(text => {
            contentCache.set(url, text);
            return navigator.clipboard.writeText(text);
          })
          .then(() => {
            button.classList.add('copied');
            setTimeout(() => button.classList.remove('copied'), 1000);
          })
          .catch(error => console.error('Failed to copy markdown:', error));
      }
    });
  });

  // Initialize dropdown toggles
  const dropdownToggles = document.querySelectorAll('.hextra-page-context-menu-toggle');
  dropdownToggles.forEach(toggle => {
    const container = toggle.closest('.hextra-page-context-menu');
    const menu = container.querySelector('.hextra-page-context-menu-dropdown');
    const chevron = toggle.querySelector('[data-chevron]');

    toggle.addEventListener('click', (e) => {
      e.stopPropagation();
      const isOpen = toggle.dataset.state === 'open';

      // Close all other dropdowns first
      dropdownToggles.forEach(t => {
        if (t !== toggle) {
          t.dataset.state = 'closed';
          t.setAttribute('aria-expanded', 'false');
          const otherContainer = t.closest('.hextra-page-context-menu');
          const otherMenu = otherContainer.querySelector('.hextra-page-context-menu-dropdown');
          const otherChevron = t.querySelector('[data-chevron]');
          otherMenu.classList.add('hx:hidden');
          if (otherChevron) {
            otherChevron.style.transform = '';
          }
        }
      });

      // Toggle current
      toggle.dataset.state = isOpen ? 'closed' : 'open';
      toggle.setAttribute('aria-expanded', isOpen ? 'false' : 'true');
      menu.classList.toggle('hx:hidden', isOpen);

      // Rotate chevron icon
      if (chevron) {
        chevron.style.transform = isOpen ? '' : 'rotate(180deg)';
      }
    });
  });

  // Close dropdown when clicking outside
  document.addEventListener('click', (e) => {
    // Check if click is outside any dropdown container
    const isOutside = !e.target.closest('.hextra-page-context-menu');
    if (isOutside) {
      dropdownToggles.forEach(toggle => {
        toggle.dataset.state = 'closed';
        toggle.setAttribute('aria-expanded', 'false');
        const container = toggle.closest('.hextra-page-context-menu');
        const menu = container.querySelector('.hextra-page-context-menu-dropdown');
        const chevron = toggle.querySelector('[data-chevron]');
        menu.classList.add('hx:hidden');
        if (chevron) {
          chevron.style.transform = '';
        }
      });
    }
  });

  // Close dropdown on Escape key and return focus to toggle
  document.addEventListener('keydown', (e) => {
    if (e.key === 'Escape') {
      dropdownToggles.forEach(toggle => {
        if (toggle.dataset.state === 'open') {
          const container = toggle.closest('.hextra-page-context-menu');
          closeDropdown(container);
          toggle.focus();
        }
      });
    }
  });

  // Helper to close dropdown
  const closeDropdown = (container) => {
    if (!container) return;
    
    const toggle = container.querySelector('.hextra-page-context-menu-toggle');
    const menu = container.querySelector('.hextra-page-context-menu-dropdown');
    
    if (!toggle || !menu) return;
    
    const chevron = toggle.querySelector('[data-chevron]');
    toggle.dataset.state = 'closed';
    toggle.setAttribute('aria-expanded', 'false');
    menu.classList.add('hx:hidden');
    if (chevron) {
      chevron.style.transform = '';
    }
  };

  // Handle dropdown menu copy action
  document.querySelectorAll('.hextra-page-context-menu-dropdown button[data-action="copy"]').forEach(btn => {
    btn.addEventListener('click', async (e) => {
      e.stopPropagation();
      const container = btn.closest('.hextra-page-context-menu');
      if (!container) return;
      
      const copyBtn = container.querySelector('.hextra-page-context-menu-copy');
      if (!copyBtn) return;

      closeDropdown(container);
      copyBtn.click();
    });
  });

  // Handle dropdown menu view action
  document.querySelectorAll('.hextra-page-context-menu-dropdown button[data-action="view"]').forEach(btn => {
    btn.addEventListener('click', (e) => {
      e.stopPropagation();
      const container = btn.closest('.hextra-page-context-menu');
      if (!container) return;
      
      const url = btn.dataset.url;
      if (!url) return;

      closeDropdown(container);
      window.open(url, '_blank', 'noopener,noreferrer');
    });
  });
});

;
document.addEventListener("DOMContentLoaded", function () {
  scrollToActiveItem();
  enableCollapsibles();
});

function enableCollapsibles() {
  const buttons = document.querySelectorAll(".hextra-sidebar-collapsible-button");
  buttons.forEach(function (button) {
    button.addEventListener("click", function (e) {
      e.preventDefault();
      const list = button.closest('li');
      if (list) {
        list.classList.toggle("open");
        button.setAttribute('aria-expanded', list.classList.contains('open') ? 'true' : 'false');
      }
    });
  });
}

function scrollToActiveItem() {
  const sidebarScrollbar = document.querySelector("aside.hextra-sidebar-container > .hextra-scrollbar");
  const activeItems = document.querySelectorAll(".hextra-sidebar-active-item");
  const visibleActiveItem = Array.from(activeItems).find(function (activeItem) {
    return activeItem.getBoundingClientRect().height > 0;
  });

  if (!visibleActiveItem) {
    return;
  }

  const yOffset = visibleActiveItem.clientHeight;
  const yDistance = visibleActiveItem.getBoundingClientRect().top - sidebarScrollbar.getBoundingClientRect().top;
  sidebarScrollbar.scrollTo({
    behavior: "instant",
    top: yDistance - yOffset
  });
}

;
function computeMenuTranslation(switcher, optionsElement) {
  // Calculate the position of a language options element.
  const switcherRect = switcher.getBoundingClientRect();

  // Must be called before optionsElement.clientWidth.
  optionsElement.style.minWidth = `${Math.max(switcherRect.width, 50)}px`;

  const isOnTop = switcher.dataset.location === 'top';
  const isOnBottom = switcher.dataset.location === 'bottom';
  const isOnBottomRight = switcher.dataset.location === 'bottom-right';
  const isRTL = document.documentElement.dir === 'rtl'

  // Stuck on the left side of the switcher.
  let x = switcherRect.left;

  if (isOnTop && !isRTL || isOnBottom && isRTL || isOnBottomRight && !isRTL) {
    // Stuck on the right side of the switcher.
    x = switcherRect.right - optionsElement.clientWidth;
  }

  // Stuck on the top of the switcher.
  let y = switcherRect.top - window.innerHeight - 10;

  if (isOnTop) {
    // Stuck on the bottom of the switcher.
    y = switcherRect.top - window.innerHeight + optionsElement.clientHeight + switcher.clientHeight + 4;
  }

  return { x: x, y: y };
}

function toggleMenu(switcher) {
  const optionsElement = switcher.nextElementSibling;

  optionsElement.classList.toggle('hx:hidden');

  // Calculate the position of a language options element.
  const translate = computeMenuTranslation(switcher, optionsElement);

  optionsElement.style.transform = `translate3d(${translate.x}px, ${translate.y}px, 0)`;
}

function resizeMenu(switcher) {
  const optionsElement = switcher.nextElementSibling;

  if (optionsElement.classList.contains('hx:hidden')) return;

  // Calculate the position of a language options element.
  const translate = computeMenuTranslation(switcher, optionsElement);

  optionsElement.style.transform = `translate3d(${translate.x}px, ${translate.y}px, 0)`;
}

;
(function () {
  function updateGroup(container, index) {
    const tabs = Array.from(container.querySelectorAll('.hextra-tabs-toggle'));
    tabs.forEach((tab, i) => {
      tab.dataset.state = i === index ? 'selected' : '';
      if (i === index) {
        tab.setAttribute('aria-selected', 'true');
        tab.tabIndex = 0;
      } else {
        tab.setAttribute('aria-selected', 'false');
        tab.tabIndex = -1;
      }
    });
    const panelsContainer = container.parentElement.nextElementSibling;
    if (!panelsContainer) return;
    Array.from(panelsContainer.children).forEach((panel, i) => {
      panel.dataset.state = i === index ? 'selected' : '';
      panel.setAttribute('aria-hidden', i === index ? 'false' : 'true');
      if (i === index) {
        panel.tabIndex = 0;
      } else {
        panel.removeAttribute('tabindex');
      }
    });
  }

  const syncGroups = document.querySelectorAll('[data-tab-group]');

  syncGroups.forEach((group) => {
    const key = encodeURIComponent(group.dataset.tabGroup);
    const saved = localStorage.getItem('hextra-tab-' + key);
    if (saved !== null) {
      updateGroup(group, parseInt(saved, 10));
    }
  });

  document.querySelectorAll('.hextra-tabs-toggle').forEach((button) => {
    button.addEventListener('click', function (e) {
      const targetButton = e.currentTarget;
      const container = targetButton.parentElement;
      const index = Array.from(container.querySelectorAll('.hextra-tabs-toggle')).indexOf(
        targetButton
      );

      if (container.dataset.tabGroup) {
        // Sync behavior: update all tab groups with the same name
        const tabGroupValue = container.dataset.tabGroup;
        const key = encodeURIComponent(tabGroupValue);
        document
          .querySelectorAll('[data-tab-group="' + tabGroupValue + '"]')
          .forEach((grp) => updateGroup(grp, index));
        localStorage.setItem('hextra-tab-' + key, index.toString());
      } else {
        // Non-sync behavior: update only this specific tab group
        updateGroup(container, index);
      }
    });

    // Keyboard navigation for tabs
    button.addEventListener('keydown', function (e) {
      const container = button.parentElement;
      const tabs = Array.from(container.querySelectorAll('.hextra-tabs-toggle'));
      const currentIndex = tabs.indexOf(button);
      let newIndex;

      switch (e.key) {
        case 'ArrowRight':
        case 'ArrowDown':
          e.preventDefault();
          newIndex = (currentIndex + 1) % tabs.length;
          break;
        case 'ArrowLeft':
        case 'ArrowUp':
          e.preventDefault();
          newIndex = (currentIndex - 1 + tabs.length) % tabs.length;
          break;
        case 'Home':
          e.preventDefault();
          newIndex = 0;
          break;
        case 'End':
          e.preventDefault();
          newIndex = tabs.length - 1;
          break;
        default:
          return;
      }

      if (container.dataset.tabGroup) {
        const tabGroupValue = container.dataset.tabGroup;
        const key = encodeURIComponent(tabGroupValue);
        document
          .querySelectorAll('[data-tab-group="' + tabGroupValue + '"]')
          .forEach((grp) => updateGroup(grp, newIndex));
        localStorage.setItem('hextra-tab-' + key, newIndex.toString());
      } else {
        updateGroup(container, newIndex);
      }
      tabs[newIndex].focus();
    });
  });
})();

;
document.addEventListener("DOMContentLoaded", function () {
  // Hugo task lists render bare checkboxes; provide an accessible name.
  document.querySelectorAll("main#content li > input[type='checkbox']").forEach(function (checkbox) {
    if (checkbox.hasAttribute("aria-label") || checkbox.hasAttribute("aria-labelledby")) {
      return;
    }
    var listItem = checkbox.closest("li");
    if (!listItem) return;

    var labelText = listItem.textContent.replace(/\s+/g, " ").trim();
    if (labelText) {
      checkbox.setAttribute("aria-label", labelText);
    }
  });
});

;
// Light / Dark theme toggle
(function () {
  const defaultTheme = 'system'
  const themes = ["light", "dark"];

  const themeToggleButtons = document.querySelectorAll(".hextra-theme-toggle");
  const themeToggleOptions = document.querySelectorAll(".hextra-theme-toggle-options button[role=menuitemradio]");

  function applyTheme(theme) {
    theme = themes.includes(theme) ? theme : "system";

    themeToggleButtons.forEach((btn) => btn.parentElement.dataset.theme = theme );
    themeToggleOptions.forEach((option) => {
      option.setAttribute('aria-checked', option.dataset.item === theme ? 'true' : 'false');
    });

    localStorage.setItem("color-theme", theme);
  }

  function switchTheme(theme) {
    setTheme(theme);
    applyTheme(theme);
  }

  const colorTheme = "color-theme" in localStorage ? localStorage.getItem("color-theme") : defaultTheme;
  switchTheme(colorTheme);

  // Add click event handler to the menu items.
  themeToggleOptions.forEach((option) => {
    option.addEventListener("click", function (e) {
      e.preventDefault();

      switchTheme(option.dataset.item);
    })
  })

  // Add click event handler to the buttons
  themeToggleButtons.forEach((toggler) => {
    toggler.addEventListener("click", function (e) {
      e.preventDefault();

      toggler.dataset.state = toggler.dataset.state === 'open' ? 'closed' : 'open';
      toggleMenu(toggler);
      const isOpen = toggler.dataset.state === 'open';
      toggler.setAttribute('aria-expanded', isOpen ? 'true' : 'false');

      // Focus first menuitem when opening
      if (isOpen) {
        const firstItem = toggler.nextElementSibling.querySelector('button[role=menuitemradio]');
        if (firstItem) firstItem.focus();
      }
    });
  });

  window.addEventListener("resize", () => themeToggleButtons.forEach(resizeMenu))

  // Dismiss the menu when clicking outside
  document.addEventListener('click', (e) => {
    if (e.target.closest('.hextra-theme-toggle') === null) {
      themeToggleButtons.forEach((toggler) => {
        toggler.dataset.state = 'closed';
        toggler.setAttribute('aria-expanded', 'false');
        toggler.nextElementSibling.classList.add('hx:hidden');
      });
    }
  });

  // Keyboard navigation for the theme menu
  document.querySelectorAll('.hextra-theme-toggle-options[role=menu]').forEach(function (menu) {
    menu.addEventListener('keydown', function (e) {
      const items = Array.from(menu.querySelectorAll('button[role=menuitemradio]'));
      const currentIndex = items.indexOf(document.activeElement);
      let newIndex;

      switch (e.key) {
        case 'ArrowDown':
          e.preventDefault();
          newIndex = (currentIndex + 1) % items.length;
          items[newIndex].focus();
          break;
        case 'ArrowUp':
          e.preventDefault();
          newIndex = (currentIndex - 1 + items.length) % items.length;
          items[newIndex].focus();
          break;
        case 'Home':
          e.preventDefault();
          items[0].focus();
          break;
        case 'End':
          e.preventDefault();
          items[items.length - 1].focus();
          break;
        case 'Escape':
          e.preventDefault();
          var toggler = menu.previousElementSibling;
          toggler.dataset.state = 'closed';
          toggler.setAttribute('aria-expanded', 'false');
          menu.classList.add('hx:hidden');
          toggler.focus();
          break;
      }
    });
  });

  // Listen for system theme changes
  window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => {
    if (localStorage.getItem("color-theme") === "system") {
      setTheme("system");
    }
  });
})();

;
/**
 * TOC Scroll - Highlights active TOC links based on visible headings
 * 
 * Uses Intersection Observer to track heading visibility and applies
 * 'hextra-toc-active' class to corresponding TOC links. Selects the
 * topmost heading when multiple are visible.
 * 
 * Requires: .hextra-toc element, matching heading IDs, toc.css styles
 */
document.addEventListener("DOMContentLoaded", function () {
  const toc = document.querySelector(".hextra-toc");
  if (!toc) return;

  const tocLinks = toc.querySelectorAll('a[href^="#"]');
  if (tocLinks.length === 0) return;

  const headingIds = Array.from(tocLinks).map((link) => link.getAttribute("href").substring(1));

  const headings = headingIds.map((id) => document.getElementById(decodeURIComponent(id))).filter(Boolean);
  if (headings.length === 0) return;

  let currentActiveLink = null;
  let isHashNavigation = false;

  // Create intersection observer
  const observer = new IntersectionObserver(
    (entries) => {
      // Skip observer updates during hash navigation
      if (isHashNavigation) return;

      const visibleHeadings = entries.filter((entry) => entry.isIntersecting).map((entry) => entry.target);

      if (visibleHeadings.length === 0) return;

      // Find the heading closest to the top of the viewport
      const topMostHeading = visibleHeadings.reduce((closest, heading) => {
        const headingTop = heading.getBoundingClientRect().top;
        const closestTop = closest.getBoundingClientRect().top;
        return Math.abs(headingTop) < Math.abs(closestTop) ? heading : closest;
      });

      // Encode the id and make it lowercase to match the TOC link
      const targetId = encodeURIComponent(topMostHeading.id).toLowerCase();
      const targetLink = toc.querySelector(`a[href="#${targetId}"]`);

      if (targetLink && targetLink !== currentActiveLink) {
        // Remove active class from previous link
        if (currentActiveLink) {
          currentActiveLink.classList.remove("hextra-toc-active");
          currentActiveLink.removeAttribute("aria-current");
        }

        // Add active class to current link
        targetLink.classList.add("hextra-toc-active");
        targetLink.setAttribute("aria-current", "location");
        currentActiveLink = targetLink;
      }
    },
    {
      rootMargin: "-20px 0px -60% 0px", // Adjust sensitivity
      threshold: [0, 0.1, 0.5, 1],
    }
  );

  // Observe all headings
  headings.forEach((heading) => observer.observe(heading));

  // Handle direct navigation to page with hash
  function handleHashNavigation() {
    const hash = window.location.hash; // already url encoded
    if (hash) {
      const targetLink = toc.querySelector(`a[href="${hash}"]`);
      if (targetLink) {
        // Disable observer temporarily during hash navigation
        isHashNavigation = true;

        if (currentActiveLink) {
          currentActiveLink.classList.remove("hextra-toc-active");
          currentActiveLink.removeAttribute("aria-current");
        }
        targetLink.classList.add("hextra-toc-active");
        targetLink.setAttribute("aria-current", "location");
        currentActiveLink = targetLink;

        // Re-enable observer after scroll settles
        setTimeout(() => { isHashNavigation = false; }, 500);
        return;
      }
    }
  }

  // Handle hash changes navigation
  window.addEventListener("hashchange", handleHashNavigation);

  // Handle initial load
  setTimeout(handleHashNavigation, 100);
});
