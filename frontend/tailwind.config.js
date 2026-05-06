/** @type {import('tailwindcss').Config} */
export default {
  content: ['./index.html', './src/**/*.{ts,tsx}'],
  theme: {
    extend: {
      fontFamily: {
        title: ['Cormorant Garamond', 'Georgia', 'serif'],
        inter: ['Cormorant Garamond', 'Georgia', 'serif'],
      },
      colors: {
        page: '#FAFAFA',
        heading: '#111111',
        body: '#444444',
        node: '#FFFFFF',
        'node-highlight': '#EEF3FF',
        'code-bg': '#000C18',
        border: '#111111',
      },
      boxShadow: {
        box: '3px 3px 0 rgba(0,0,0,0.08)',
      },
      fontSize: {
        'website-title': ['4rem', { lineHeight: '1.1', fontWeight: '400' }],
        'webpage-title': ['3rem', { lineHeight: '1.1', fontWeight: '700' }],
        h2: ['1.75rem', { lineHeight: '1.2', fontWeight: '700' }],
        h3: ['1.25rem', { lineHeight: '1.3', fontWeight: '700' }],
        para: ['0.9375rem', { lineHeight: '1.7', fontWeight: '400' }],
      },
    },
  },
  plugins: [],
}
