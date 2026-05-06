import Navigation from '../components/Navigation'
import { methodsContent } from '../data/content'

export default function MethodsPage() {
  return (
    <div
      className="min-h-screen"
      style={{ background: '#FAFAFA', paddingTop: '5rem', paddingBottom: '5rem' }}
    >
      <Navigation />

      <div style={{ maxWidth: 820, margin: '0 auto', padding: '0 2rem' }}>
        {/* Page title */}
        <h1
          className="font-inter font-bold text-center text-[#111111]"
          style={{ fontSize: '3rem', lineHeight: 1.1, margin: '0 0 4rem' }}
        >
          Methods
        </h1>

        {/* Two-column methods section */}
        <section style={{ marginBottom: '4rem' }}>
          <div
            style={{
              display: 'grid',
              gridTemplateColumns: '1fr 1fr',
              gap: '3rem',
            }}
          >
            <div>
              <h3
                className="font-inter font-bold text-[#444444]"
                style={{ fontSize: '1.25rem', margin: '0 0 1rem' }}
              >
                Initial
              </h3>
              <p
                className="font-inter text-[#444444]"
                style={{ fontSize: '0.9375rem', lineHeight: 1.75, margin: 0 }}
              >
                {methodsContent.initial}
              </p>
            </div>

            <div>
              <h3
                className="font-inter font-bold text-[#444444]"
                style={{ fontSize: '1.25rem', margin: '0 0 1rem' }}
              >
                Final
              </h3>
              <p
                className="font-inter text-[#444444]"
                style={{ fontSize: '0.9375rem', lineHeight: 1.75, margin: 0 }}
              >
                {methodsContent.final}
              </p>
            </div>
          </div>
        </section>

        {/* GitHub section */}
        <section style={{ textAlign: 'center' }}>
          <h3
            className="font-inter font-bold text-[#444444]"
            style={{ fontSize: '1.25rem', margin: '0 0 0.75rem' }}
          >
            {methodsContent.githubLabel}
          </h3>
          <a
            href={methodsContent.githubUrl}
            target="_blank"
            rel="noopener noreferrer"
            className="font-inter text-[#111111] underline hover:opacity-70 transition-opacity"
            style={{ fontSize: '0.9375rem', wordBreak: 'break-all' }}
          >
            {methodsContent.githubUrl}
          </a>
        </section>
      </div>
    </div>
  )
}
