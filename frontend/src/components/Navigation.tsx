import { useState, useEffect, useRef } from 'react'
import { Link, useLocation } from 'react-router-dom'

const ALL_PAGES = [
  { path: '/',             label: 'Home' },
  { path: '/main-theorem', label: 'Main Theorem' },
  { path: '/about',        label: 'About' },
  { path: '/methods',      label: 'Thoughts & Lessons' },
]

export default function Navigation() {
  const [open, setOpen] = useState(false)
  const location = useLocation()
  const ref = useRef<HTMLDivElement>(null)

  const otherPages = ALL_PAGES.filter(p => p.path !== location.pathname)

  useEffect(() => {
    function handleClick(e: MouseEvent) {
      if (ref.current && !ref.current.contains(e.target as Node)) {
        setOpen(false)
      }
    }
    if (open) document.addEventListener('mousedown', handleClick)
    return () => document.removeEventListener('mousedown', handleClick)
  }, [open])

  return (
    <div ref={ref} className="fixed top-4 right-4 z-40">
      {/* Hamburger button */}
      <button
        onClick={() => setOpen(o => !o)}
        aria-label="Navigation menu"
        className="flex flex-col justify-center items-center gap-1.5 w-9 h-9 p-1.5 hover:opacity-70 transition-opacity"
      >
        <span className="block w-5 h-px bg-[#444444]" />
        <span className="block w-5 h-px bg-[#444444]" />
        <span className="block w-5 h-px bg-[#444444]" />
      </button>

      {/* Slide-out dropdown */}
      {open && (
        <div
          className="absolute top-10 right-0 bg-white border border-[#111111] shadow-box py-3 min-w-[160px]"
          style={{ boxShadow: '3px 3px 0 rgba(0,0,0,0.08)' }}
        >
          {otherPages.map(page => (
            <Link
              key={page.path}
              to={page.path}
              onClick={() => setOpen(false)}
              className="block px-5 py-2 text-para text-[#444444] hover:text-[#111111] hover:bg-[#F5F5F5] transition-colors"
              style={{ fontSize: '0.9375rem' }}
            >
              {page.label}
            </Link>
          ))}
        </div>
      )}
    </div>
  )
}
