import Navigation from '../components/Navigation'
import { aboutContent } from '../data/content'

export default function AboutPage() {
  return (
    <div
      className="min-h-screen"
      style={{ background: '#FAFAFA', paddingTop: '5rem', paddingBottom: '5rem' }}
    >
      <Navigation />

      <div style={{ maxWidth: 680, margin: '0 auto', padding: '0 2rem' }}>
        {/* Page title */}
        <h1
          className="font-inter font-bold text-center text-[#111111]"
          style={{ fontSize: '3rem', lineHeight: 1.1, margin: '0 0 4rem' }}
        >
          About
        </h1>

        {/* Goals section */}
        <section style={{ marginBottom: '4rem' }}>
          <h2
            className="font-inter font-bold text-center text-[#111111]"
            style={{ fontSize: '1.75rem', lineHeight: 1.2, margin: '0 0 1.25rem' }}
          >
            Goals
          </h2>
          <p
            className="font-inter text-center text-[#444444]"
            style={{ fontSize: '0.9375rem', lineHeight: 1.75, margin: 0 }}
          >
            {aboutContent.goals}
          </p>
        </section>

        {/* Authors section */}
        <section>
          <h2
            className="font-inter font-bold text-center text-[#111111]"
            style={{ fontSize: '1.75rem', lineHeight: 1.2, margin: '0 0 2rem' }}
          >
            Authors
          </h2>

          <div
            className="flex justify-center gap-12"
            style={{ flexWrap: 'wrap' }}
          >
            {aboutContent.authors.map(author => (
              <div key={author.name} className="flex flex-col items-center gap-3">
                {/* Photo or placeholder circle */}
                {author.photoSrc ? (
                  <img
                    src={author.photoSrc}
                    alt={author.name}
                    style={{
                      width: 120,
                      height: 120,
                      borderRadius: '50%',
                      objectFit: 'cover',
                      border: '1px solid #cccccc',
                    }}
                  />
                ) : (
                  <div
                    style={{
                      width: 120,
                      height: 120,
                      borderRadius: '50%',
                      background: '#D8D8D8',
                      border: '1px solid #bbbbbb',
                    }}
                  />
                )}
                <p
                  className="font-inter font-bold text-center text-[#444444]"
                  style={{ fontSize: '0.9375rem', margin: 0 }}
                >
                  {author.name}
                </p>
              </div>
            ))}
          </div>
        </section>
      </div>
    </div>
  )
}
